{-# LANGUAGE TypeOperators #-}
module Clausify
  (  clausifyForms,            --  Index -> [Form Name] ->   (Cache,Index,[Clause Name],[ImplClause Name])
     closureImplClauses        --  [ImplClause Name] -> [Clause Name]
  )
 where


import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List 
import Control.Monad.State

import Language
import ProverTypes -- Cache


-- New names have the form "$pk", with k >= 0
-- To make a new name, use function mkNewName :: Int -> Name

--  SIMPLE FORMULA sf
--  sf ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
--           p1, p2 atoms

data ClausState =
  ClaussState{
    clausCache :: Map.Map SimpleForm  Name ,  -- map  simple form  |-- name (local cache)
    clausIndex :: Int,    -- index of the next new name 
    clausCs :: Set.Set (Clause Name),  --      clauses         created during clausification
    clausIcs :: Set.Set (ImplClause Name), --  impl. clauese   created during clausification
    clausCountReducedIcs :: Int
    }         

mkClausState :: Int -> ClausState
mkClausState index =
  ClaussState{
    clausCache  = Map.empty,
    clausIndex = index, 
    clausCs = Set.empty,
    clausIcs = Set.empty,
    clausCountReducedIcs = 0
    }     





clausifyForms ::  Index -> [Form Name] ->   (Cache, Index,[Clause Name],[ImplClause Name])
-- Clausify the input formulas starting new names with index.
-- Return (cache,newIndex,cs,ics) where:
--  cache stores the map simple form |-- name 
--  newIndex is the next index to be used for new names
--  (cs,ics,mainGoalName) is the clausification of the input formulas (mainGoalName = "$goal")
clausifyForms index forms =
  let
    finalClausSt = execState (mclausifyForms forms) (mkClausState index)
    finalCache = clausCache finalClausSt
    newIndex = clausIndex finalClausSt 
    cs  = Set.toList $ clausCs finalClausSt 
    ics = Set.toList $ clausIcs  finalClausSt
    -- countReducedIcs = clausCountReducedIcs finalClausSt
  in     
  (invertMap finalCache,newIndex,cs,ics)       

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap m =
   Map.fromList $ map swap (Map.toList m )
   where swap(a,b) = (b,a)


mclausifyForms ::  [Form Name] ->  State ClausState ()
-- clausification of a list of formulas
mclausifyForms  fs =
  sequence_ [ clausifyForm (simplify f) | f <- fs ] 


closureImplClauses :: [ImplClause Name] -> [Clause Name]
-- closureImplClauses Ics = { b => c |  (a => b ) => c \in ics } 
-- We avoid trivial clauses, namely: b == false, b == c
closureImplClauses ics =
   [ [b] :=> [c] | (a :-> b ) :-> c <- ics, b /= false, b /= c  ]



{-

REDUCE IMPLICATION CLAUSES WITH SAME ANTECEDENT

Clauses with the same antecedent are reduced as follows:

  (a => b) => x1  ...   (a => b) => xn

with n >= 2 are reduced to

  p => x1    ....p => xn

where p is a  name equivalent to the simple formula a => b 

-}

reduceImplClauses  ::  [ImplClause Name] ->  State ClausState ()
reduceImplClauses ics =  
  do
  let sames = Map.toList (Map.fromListWith (++) [ (a:->b,[x]) | ((a:->b):->x) <- ics ])
  --  sames is the list of pairs
  --      ( (a => b, [x1 .. xn] ) 
  --  such that  (a => b) => x1, .... , (a=>b)=>xn are all the ic in ics  having antecedent a => b    
  if (any ( \ (a:->b, xs) -> length xs > 1) sames ) then
    -- at least an ic to reduce
        reduceImplClausesSameAnt sames
  else
   -- nothing to reduce
     return ()


type SameAnt =  ( (Name :-> Name), [Name] )
--    ( (a => b), [x1 .. xn] ) represent the list of clauses
--   (a => b) => x1, ... , (a=>b) => xn
--   having the same antecedent a =>  b

reduceImplClausesSameAnt :: [SameAnt]   -> State ClausState ()

reduceImplClausesSameAnt [] = return () 

reduceImplClausesSameAnt ( (a :-> b,[x])  : sames) =
 -- (a => b,[x]) does not require reduction 
 reduceImplClausesSameAnt sames

reduceImplClausesSameAnt ( (a :-> b,xs)  : sames) =
--  length xs >= 2 
  do
    clausSt <- get
    p <- nameEquivWith_simpleForm ( a :==>: b)
    let  newCs  = [ [p] :=> [x] | x <- xs ]
         n = clausCountReducedIcs clausSt
    addClauses newCs
    modify ( \s ->  s{ clausCountReducedIcs = n  + length xs } )
    reduceImplClausesSameAnt sames



--------------------------------------------------------



goalify :: [Input (Form Name)] -> [Form Name]
{-

Given a list of input formulas containing

  (Input  _ Axiom f1)
   ...
  (Input _ Axiom fn)
  (Input  _ Conjecture (g1 :=>: .. :=>  g(m-1) :=> gm)  ) 

(in any order) return a list containing the formulas

  f1 ... fn, g1 ..  g(m-1),  (gm :=>: mainGoalName) 

where mainGoalName = "$goal".

ASSUMPION: mainGoalName does not occurr in the input formulas

Note that the formulas

  ( f1 & ... & fn)   :=>:  (g1 :=>: .. :=>  g(m-1) :=> gm)

and

 ( f1 &... & fn & g1 ..  g(m-1)  &  (gm :=>: mainGoalName) )  :=>: mainGoalName

are equisatisfaiable in IPL


-}



goalify []  = []
goalify ( (Input str Axiom f)  : iforms) = f : goalify iforms
goalify ( (Input str Conjecture f) : iforms ) =
  case f of
    f1 :=>: f2   -> f1 : goalify ( (Input str Conjecture f2) : iforms)
    _            -> (f :=>: Atom mainGoalName) : goalify iforms



--------------------------------------------------------------------------------
-- simplify:
-- 1) logical constants TRUE and FALSE
-- 2) equal subformulas (e.g., f & f |---> f )

simplify :: Form Name -> Form Name
simplify (f1 :&: f2) = simplify f1 .&. simplify f2
 where
  f1 .&. f2 | f1 == f2 = f1
  TRUE  .&. f2     = f2
  f1     .&. TRUE  = f1
  FALSE .&. f2     = FALSE
  f1     .&. FALSE = FALSE
  f1     .&. f2     = f1 :&: f2

simplify (f1 :|: f2) = simplify f1 .|. simplify f2
 where
  f1 .|. f2 | f1 == f2 = f1
  TRUE  .|. f2     = TRUE
  f1     .|. TRUE  = TRUE
  FALSE .|. f2     = f2
  f1     .|. FALSE = f1
  f1     .|. f2     = f1 :|: f2

simplify (f1 :=>: f2) = simplify f1 .=>. simplify f2
 where
  f1 .=>. f2 | f1 == f2 = TRUE
  TRUE  .=>. f2     = f2
  f1     .=>. TRUE  = TRUE
  FALSE .=>. f2     = TRUE
  f1     .=>. FALSE = f1 :=>: Atom false -- cannot be simplified away
  f1     .=>. f2     = f1 :=>: f2

simplify (f1 :<=>: f2) = simplify f1 .<=>. simplify f2
 where
  f1 .<=>. f2 | f1 == f2 = TRUE
  TRUE  .<=>. f2     = f2
  f1     .<=>. TRUE  = f1
  FALSE .<=>. f2     = f2 :=>: Atom false
  f1     .<=>. FALSE = f1 :=>: Atom false
  f1     .<=>. f2     = f1 :<=>: f2

simplify f = f



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- CLAUSIFICATION OF A FORMULA
-- The clausification procedure updates the state
clausifyForm :: Form Name -> State ClausState ()
-- any formula
clausifyForm TRUE        =  return ()  -- do nothing
clausifyForm FALSE       =  addClause ([] :=> []) -- add null clause
clausifyForm (Atom a)    =  addClause ([] :=> [a])

clausifyForm (f1 :&: f2)  =
  clausifyForm f1 >> clausifyForm f2

clausifyForm (f1 :<=>: f2) =
  do p1 <- nameEquivWith f1
     p2 <- nameEquivWith f2
     addClauses [ [p1] :=> [p2] , [p2] :=> [p1] ]

clausifyForm (f1 :|: f2)   = clausifyOr [] [f1,f2]
clausifyForm (f1 :=>: f2)  = clausifyImpl f1 f2

clausifyOr :: [Name] -> [Form Name] -> State ClausState ()
-- clausifyOr [p1 .. pm] [f1 ... fn]  (with p1 ... pm atoms, f1 .. fn any formulas)
-- clausify  the formula
--   p1 | ... pm | f1 ... fn
clausifyOr ps [] =  addClause ([] :=> ps)
clausifyOr ps ((f1 :|: f2) : fs) =  clausifyOr ps (f1 : f2 : fs)
clausifyOr ps (f1 : fs) =
  do p1 <- nameEquivWith f1
     clausifyOr (p1:ps) fs

clausifyImpl :: Form Name -> Form Name -> State ClausState ()
-- clausifyImpl f1 f2
-- clausify the formula f1 => f2
clausifyImpl (Atom a)  (Atom b)   = addClause ([a] :=> [b])

clausifyImpl (Atom a)  (f1 :&: f2)  = clausifyImpl (Atom a) f1 >> clausifyImpl (Atom a) f2
clausifyImpl (f1 :|: f2) (Atom b)   = clausifyImpl f1 (Atom b) >> clausifyImpl f2 (Atom b)

clausifyImpl f1  (f2 :=>: f3) = clausifyImpl (f1 :&: f2) f3

clausifyImpl (f1:=>:f2)  f3 =
  do p1 <- nameEquivWith f1
     p2 <- nameEquivWith f2
     p3 <- nameEquivWith f3
     addImplClause ((p1:->p2):->p3)

clausifyImpl f1 f2  =
  do p1s <- namesAnd f1
     p2s <- namesOr  f2
     addClause (p1s :=> p2s)

namesAnd :: Form Name ->  State ClausState  [Name]
-- namesAnd (f1 & ... & fn)
-- [p1 ... pn] such that pk is a name for fk, for every 1 <= k <= n
namesAnd (f1 :&: f2) =
  do p1s <- namesAnd f1
     p2s <- namesAnd f2
     return (p1s ++ p2s)
namesAnd f =
  do p <- nameEquivWith f
     return [p]

namesOr :: Form Name -> State ClausState  [Name]
-- namesOr (f1 | ... | fn)
-- [p1 ... pn] such that pk is a name for fk, for every 1 <= k <= n
namesOr (f1 :|: f2) =
  do p1s <- namesOr f1
     p2s <- namesOr f2
     return (p1s ++ p2s)
namesOr f  =
  do p <- nameEquivWith f
     return [p]

nameEquivWith :: Form Name -> State ClausState Name
-- return a name equivalent with f, possibly updating the state
nameEquivWith  (Atom a) = return a

nameEquivWith  (f1 :&: f2) =
--  p1 |--> f1
--  p2 |--> f2  
--   q |--> f1 & f2
--  NEW  CS:  q => p1, q => p2, p1 & p2 => q 
  do p1 <- nameEquivWith  f1
     p2 <- nameEquivWith  f2
     q  <- nameEquivWith_simpleForm  (p1 :&&: p2)
     addClauses [ [q]   :=> [p1] , [q]   :=> [p2] , [p1,p2] :=> [q] ]
     return q

nameEquivWith (f1 :|: f2) =
--  p1 |--> f1
--  p2 |--> f2  
--   q |--> f1 | f2
--  NEW  CS:  q => p1 | p2,  p1  => q,  p2 => q 
  do p1 <- nameEquivWith  f1
     p2 <- nameEquivWith  f2
     q  <- nameEquivWith_simpleForm  (p1 :||: p2)
     addClauses [ [q] :=> [p1,p2] , [p1] :=> [q] , [p2] :=> [q] ]
     return q

nameEquivWith  (f1 :=>: f2) =
--  p1 |--> f1
--  p2 |--> f2  
--   q |--> f1 => f2
--  NEW  CS:  q & p1 =>  p2
--  NEW ICS:  (p1 => p2) => q  
  do p1 <- nameEquivWith  f1 
     p2 <- nameEquivWith  f2
     q  <- nameEquivWith_simpleForm  (p1 :==>: p2)
     addClause  ([q,p1] :=> [p2])
     addImplClause ((p1:->p2) :-> q)
     return q

nameEquivWith  (f1 :<=>: f2) =
--  p1 |-->  f1
--  p2 |-->  f2  
--   q |-->  f1 <=> f2
--  q1 |-->  p1 => p2
--  q2 |-->  p2 => p1  
--  NEW  CS:   q & p1 =>  p2,   q & p2 =>  p1
--            q1 & p1 =>  p2,  q2 & p2 =>  p1
--            q1 & q2 => q  
--  NEW ICS:  (p1 => p2) => q1,  (p2 => p1) => q2   
  do p1 <- nameEquivWith f1
     p2 <- nameEquivWith f2
     q1 <- nameEquivWith_simpleForm (p1 :==>: p2)
     q2 <- nameEquivWith_simpleForm (p2 :==>: p1)
     q  <- nameEquivWith_simpleForm (p1 :<==>: p2)
     addClauses [
       [q,p1] :=> [p2] , [q,p2] :=> [p1] , [q1,p1] :=> [p2],
       [q2,p2] :=> [p1],  [q1,q2] :=> [q], [q1,q2] :=> [q]
      ]
     addImplClauses [ (p1:->p2) :-> q1 ,  (p2:->p1) :-> q2 ]
     return q


normalForm :: SimpleForm -> SimpleForm
-- simple form ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
--                  p1, p2 atoms
normalForm  (p1 :&&: p2)   | p1 > p2 = p2 :&&: p1
normalForm  (p1 :||: p2)   | p1 > p2 = p2 :||: p1
normalForm  (p1 :<==>: p2) | p1 > p2 = p2 :<==>: p1
normalForm  sf = sf

nameEquivWith_simpleForm :: SimpleForm -> State ClausState  Name
-- return a name equivalen with a simple form, by inspecting (and possibly updating) the cache
nameEquivWith_simpleForm sf =
  do
    clausSt <- get
    let normal_sf = normalForm sf
        cache =  clausCache clausSt 
    case Map.lookup  normal_sf cache  of
       Just p -> return p
       Nothing ->
        do
          let n = clausIndex clausSt
              newName = mkNewName n
              newCache = Map.insert normal_sf newName cache 
          modify( \s ->  s{clausCache = newCache, clausIndex = n + 1 } ) 
          return newName      

addClause :: Clause Name -> State ClausState ()
addClause c =
  modify( \s -> s{ clausCs = Set.insert c (clausCs s) })

addClauses :: [Clause Name] -> State ClausState ()
addClauses cs =
  sequence_ [ addClause c | c <- cs ]
  
addImplClause :: ImplClause Name -> State ClausState ()
addImplClause ic =
   modify( \s -> s{ clausIcs = Set.insert ic (clausIcs s) } )

addImplClauses :: [ImplClause Name] -> State ClausState ()
addImplClauses ics =
  sequence_ [ addImplClause ic | ic <- ics ]

