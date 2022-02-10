{-# LANGUAGE TypeOperators #-}
module Language
 where

import Data.List
import Data.Maybe
import qualified Data.Map as Map



-- ######### FORMULA ##########

type Name = String
type GoalName = Name
type Index = Int

false :: Name
false = "$false"

true :: Name
true = "$true"


mainGoalName :: Name
mainGoalName = "$goal"

isNewName :: Name -> Bool
isNewName p =
  head p == '$'


data Form a 
  = TRUE
  | FALSE
  | Atom a
  | (Form a) :&: (Form a)
  | (Form a) :|: (Form a)
  | (Form a ) :=>: (Form a)
  | (Form a) :<=>: (Form a)
   deriving ( Eq, Ord )

instance (Show a) => Show (Form a) where
  show (Atom atm)    = show atm
  show (f1 :&: f2)   = "(" ++ show f1 ++ " & "   ++ show f2 ++ ")"
  show (f1 :|: f2)   = "(" ++ show f1 ++ " | "   ++ show f2 ++ ")"
  show (f1 :=>: f2)  = "(" ++ show f1 ++ " => "  ++ show f2 ++ ")"
  show (f1 :<=>: f2) = "(" ++ show f1 ++ " <=> " ++ show f2 ++ ")"
  show TRUE        =  true  --- "$true"
  show FALSE       =  false -- "$false"

instance Functor Form where
  fmap g (Atom p)    = Atom (g p)
  fmap g (f1 :&: f2)   = (fmap g f1)  :&:  (fmap g f2 )
  fmap g (f1 :|: f2)   = (fmap g f1)  :|:  (fmap g f2 )
  fmap g (f1 :=>: f2)  = (fmap g f1)  :=>:  (fmap g f2 )
  fmap g (f1 :<=>: f2) = (fmap g f1)  :<=>:  (fmap g f2 )
  fmap g TRUE        =  TRUE
  fmap g FALSE       =  FALSE 


getFormNames :: Eq a => Form a  -> [a]
getFormNames f | ( f == TRUE) || (f == FALSE) = []
getFormNames (Atom p) = [p]
getFormNames (f1 :&: f2)   = ( getFormNames f1 ) `union`  ( getFormNames f2 )
getFormNames (f1 :|: f2)   = ( getFormNames f1 ) `union`  ( getFormNames f2 )
getFormNames (f1 :=>: f2)  = ( getFormNames f1 ) `union`  ( getFormNames f2 )
getFormNames (f1 :<=>: f2) = ( getFormNames f1 ) `union`  ( getFormNames f2 )  
             
getFormsNames ::  Eq a => [Form a]  -> [a]
getFormsNames  = concatMap getFormNames 

negf :: Form a -> Form a
negf f = ( f :=>: FALSE)

multiAnd  ::  [Form a] -> Form a
-- f1 .. fn  -- >   f1 & ... & fn
multiAnd [] = TRUE
multiAnd (f : fs) =
  if null fs then f
  else f :&: multiAnd fs

multiOr  ::  [Form a] -> Form a
-- f1 .. fn  -- >   f1 | ... | fn
multiOr [] = FALSE
multiOr (f : fs) =
  if null fs then f
  else f :|: multiOr fs


buildImplication  ::  [Form a] -> [Form a] ->  Form a
-- [f1 .. fm] [g1..gn] |-->   (f1 & .. & fm) => (g1 | .. | gn)  
buildImplication fs gs =
  if null fs then multiOr gs
  else
    (multiAnd fs) :=>: (multiOr gs)

buildInputForm :: [Input (Form a)] -> Form a
{-

Given a list of input formulas

 (Input  _ Axiom f1)      ...      (Input _ Axiom fm) , (Input  _ Conjecture g) 

(in any order) return the formula

  f1 & .. & fn => g1 & ... & gn   

ASSUMPTION: there is one Conjecture

-}
buildInputForm inputForms =
  let fs = [ f | (Input _  Axiom f) <- inputForms ]
      g =  head [ f | (Input _  Conjecture f) <- inputForms ]
  in buildImplication  fs [g]


data LogicalOp = NoOp | NegOp | AndOp | OrOp | ImplOp | IffOp 
  deriving Eq

mainLogicalOp :: Form Name-> LogicalOp

mainLogicalOp  f | f == TRUE || f == FALSE = NoOp
mainLogicalOp (Atom _) = NoOp 
mainLogicalOp (f1 :&: f2 ) = AndOp
mainLogicalOp (f1 :|: f2 ) = OrOp
mainLogicalOp (f1 :=>: FALSE ) = NegOp
mainLogicalOp (f1 :=>: Atom f2 ) | f2 == false = NegOp
mainLogicalOp (f1 :=>: f2 ) = ImplOp
mainLogicalOp (f1 :<=>: f2 ) = IffOp


  
-- used to represent TPTP formulas
data Input a = Input Name FormRole a
 deriving ( Eq, Ord )

instance Show a => Show (Input a) where
  show (Input name role x) =
    "fof(" ++ name ++ ", " ++ show role ++ ", " ++ show x ++ " )."

data FormRole =
  Axiom
  | Conjecture
 deriving ( Eq, Ord )

instance Show FormRole where
  show Axiom       = "axiom"
  show Conjecture = "conjecture"


-- mkNewName :: Int -> Name
-- make the name of a new atom,  having form "$pk", with k >= 0

mkNewName :: Int -> Name
-- make the name of a new atom
mkNewName k =  "$p" ++ show k


data a :-> b = a :-> b
  deriving ( Eq, Ord )

instance (Show a, Show b) => Show (a :-> b) where
  show (x :-> y) = "(" ++ show x ++ ") -> (" ++ show y ++ ")"




data Clause a = [a] :=> [a]
   deriving ( Eq, Ord )

instance Functor Clause where
  fmap f (xs :=> ys) = (map f xs) :=> (map f ys)

getClauseNames :: Eq a => Clause a  -> [a]
getClauseNames (xs :=> ys) = nub $ xs ++ ys -- remove duplications

getClausesNames :: Eq a => [Clause a]  -> [a]
getClausesNames  = concatMap getClauseNames



type ImplClause a = (a :-> a) :-> a

instance (Show a) => Show (Clause a) where
  show (xs :=> ys) = show xs ++ " =>  " ++ show ys


fmapImplClause ::  (a -> b) -> ImplClause a -> ImplClause b
fmapImplClause f ((a :-> b):-> c) = (f a :->  f b):->  f c 

getImplClauseNames :: Eq a => ImplClause a  -> [a]
getImplClauseNames  ((a :-> b):-> c) = nub [a,b,c] -- remove duplications

getImplClausesNames :: Eq a => [ImplClause a]  -> [a]
getImplClausesNames  = concatMap getImplClauseNames


indexNewName  :: Name -> Int
-- newName: $p0, $p1, ....
-- $p0 |-> 0,   $p1 |-> 1,  $p10 |-> 10, ...
indexNewName newName =
  -- read $ fromJust $ stripPrefix "$p" newName
  read $ fromMaybe "-1" $ stripPrefix "$p" newName  -- ????????




type Cache = Map.Map Name SimpleForm 


cache_to_nameFormList :: Cache -> [(Name, Form Name)]
cache_to_nameFormList cache =
  map ( \(name,sf ) -> ( name, simpleFormToForm sf) )  (Map.toList cache)

cache_to_sortedNameFormList :: Cache -> [(Name, Form Name)]
cache_to_sortedNameFormList  cache =
  sortOn (indexNewName .fst ) ( cache_to_nameFormList cache)

cacheSize :: Cache -> Int
cacheSize  = Map.size 

data SimpleForm 
  = Name :&&: Name
  | Name :||: Name
  | Name :==>: Name
  | Name :<==>: Name
 deriving ( Eq, Ord, Show )


simpleFormToForm :: SimpleForm -> Form Name
simpleFormToForm (n1 :&&: n2)   = (Atom n1)  :&: (Atom n2)
simpleFormToForm (n1 :||: n2)   = (Atom n1)  :|: (Atom n2)
simpleFormToForm (n1 :==>: n2)  = (Atom n1)  :=>: (Atom n2)
simpleFormToForm (n1 :<==>: n2) = (Atom n1)  :<=>: (Atom n2) 



type Substitution = Map.Map Name (Form Name)


applySubst :: Substitution -> Form Name -> Form Name

applySubst subst TRUE = TRUE
applySubst subst FALSE = FALSE

applySubst subst (Atom a) =
  case Map.lookup a subst of
      Just f -> applySubst subst f
      Nothing -> Atom a

applySubst subst (f1 :&: f2) =
  (applySubst subst f1 ) :&: (applySubst subst f2)

applySubst subst (f1 :|: f2) =
  (applySubst subst f1 ) :|: (applySubst subst f2)

applySubst subst (f1 :=>: f2) =
  (applySubst subst f1 ) :=>: (applySubst subst f2)

applySubst subst (f1 :<=>: f2) =
  (applySubst subst f1 ) :&: (applySubst subst f2)


cache_to_nameFormSubstList ::  Cache ->   [(Name, Form Name)]
--  list (name,form) such that  form is the formula equivalent to name
cache_to_nameFormSubstList  cache   =
  let nameFormList = cache_to_sortedNameFormList cache
      subst = Map.fromList  nameFormList
  in  map (\(name,form) ->  (name, (applySubst subst form)) ) nameFormList

cache_to_subst  :: Cache   -> Substitution
-- substitution     extracted from the cache
cache_to_subst  = Map.fromList . cache_to_nameFormSubstList  


sortNames ::  [Name] -> [Name]  
sortNames xs =
  let (g,ys) = partition (\x -> x == "$goal") xs
      (newAtms,atms)  =  partition isNewName ys
  in sort atms ++ g ++ sortOn indexNewName newAtms  
  


t1 = ["b" , "$p15", "a" , "$p1", "$goal" , "$p2" , "$p21" ]
