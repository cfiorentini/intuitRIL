{-# LANGUAGE TypeOperators #-}

module Utility(
       trueAtmsInSat,      -- Solver -> [Lit] -> IO [Lit]
       getNames,           --  [Clause Name] -> [ImplClause Name] -> GoalName  -> [Name]
       satAddClause,       -- Solver -> Clause Lit -> IO Bool
       satAddClauses,      -- Solver -> [Clause Lit] -> IO ()
       splitName,          --  Name -> (String,String)
                           -- p11 |-> (p,11) ,  p123q14 |-> (p123,14)  , pqr |-> (pqr, "")
       replaceWithInStr,   -- Char -> Char -> String -> String
       printClause,        --   Clause a -> String
       printImplClause,    --   ImplClause a -> String
       printfAtmsBrace,    --   (a -> Name) ->  [a] -> String
       printfClause,       --   (a -> Name) ->  Clause a -> String
       printfClauses,      --   (a -> Name) ->  [Clause a] -> String
       printfImplClause,   --   (a -> Name) ->  ImplClause a -> String
       printfImplClauses,  --   (a -> Name) ->  [ImplClause a] -> String
       printfImplClausesLn,  --   (a -> Name) ->  [ImplClause a] -> String
       printfForm,         --   (a -> Name) -> Form a -> String
       printfForms,        --   (a -> Name) -> [Form a] -> String
       printfFormsLn,      --   (a -> Name) -> [Form a] -> String -- print in different lines
       printCache,         --   Cache -> String
       printCacheSubst,    --   Cache -> String  print the cache with all the substitutions applied
       printCacheSubst_withMainGoal,            --  Cache ->  Form Name ->  String
       cache_to_nameFormSubstList_withMainGoal,  -- Cache ->  Form Name ->  [(Name, Form Name)]
       cache_to_subst_withMainGoal,              -- Cache ->  Form Name ->  Substitution
       printfWorld,        --    Ord a => (a -> Name) ->  World a -> String
       printfModel         --    Ord a => (a -> Name) ->  Model a -> String        
     )
   where

import Data.List     
import Data.Maybe
import MiniSat
import qualified Data.Set as Set
import qualified Data.Map as Map

import Language 
import Model


--------------------------------------------------------------------------------
---   ###  SAT SOLVER



trueAtmsInSat :: Solver -> [Lit] -> IO [Lit]
trueAtmsInSat sat univ =
-- atoms from univ which are true in the solver
  do
  vals <- sequence [ (Just True ==) `fmap` modelValue  sat x | x <-  univ  ]
  -- vals = (x,b) where b=True if x is true in sat, b=False  otherwise 
  return  [ x | (x,True) <-  univ `zip` vals ]


getNames ::  [Clause Name] -> [ImplClause Name] -> GoalName  -> [Name]
-- duplication free list of the  the names occurring in (ics,ics,goal)
-- NOTE:  Set.fromList :: Ord a => [a] -> Set    complexity O(n log n)
--                 nub ::  Eq a => [a] -> [a]    complexity O(n^2)
getNames  cs ics goal =
  Set.toList $ Set.fromList $ [ x | (xs :=> ys) <- cs, x <- xs ++ ys ]
                                ++ [ z | ((a:->b):->c) <- ics, z <- [a,b,c] ]
                                ++ [ goal, false ]


satAddClause :: Solver -> Clause Lit -> IO Bool
-- [x1, ... , xm]  :=> [y1, .... yn]
--  corresponds to the clause
-- ~x1 v ... v ~xm v y1 v ... v yn
satAddClause sat  (xs :=> ys ) =
  addClause sat ( [ neg x | x <- xs ] ++ ys  )
--  addClause :: Solver -> [Lit] -> IO Bool

satAddClauses :: Solver -> [Clause Lit] -> IO ()
satAddClauses  sat clauses  =
  mapM_ ( satAddClause sat ) clauses 



--------------------------------------------------------------------------------

-- #### PRINT (for trace)


printfListSep :: String -> (a -> String) ->  [a] -> String
-- first argument: separator between elements
printfListSep sep pf []   = "" 
printfListSep sep pf [x]   = pf x
printfListSep sep pf (x:xs)   = pf x ++ sep ++ printfListSep sep pf  xs

printfList :: (a -> String) -> [a] -> String
printfList  = printfListSep ", " 

printfListNl :: (a -> String) -> [a] -> String
printfListNl = printfListSep "\n" 


printfAtms ::   (a -> Name) ->  [a] -> String
printfAtms  pf xs = printfList pf  xs

printfAtmsSep ::  String ->  (a -> Name) ->   [a] -> String
printfAtmsSep sep  pf xs = printfListSep sep pf  xs



printfAtmsSq ::   (a -> Name) ->  [a] -> String
printfAtmsSq  pf xs = "[" ++ printfAtms pf xs ++ "]"

printfAtmsBrace ::   (a -> Name) ->  [a] -> String
printfAtmsBrace  pf xs = "{" ++ printfAtms pf xs ++ "}"

printfClause :: (a -> Name) ->   Clause a -> String
printfClause pf   ( [] :=> [] ) = false  
printfClause pf   ([] :=> ys) = printfAtmsSep " | " pf ys  
printfClause pf  (xs :=> ys) =
  printfAtmsSep " & " pf xs ++ " -> " ++ printfAtmsSep " | " pf ys  

printClause :: Clause Name -> String
printClause  = printfClause  id

printfClauses :: (a -> Name) ->  [Clause a] -> String
printfClauses pf cs =  printfListNl (printfClause pf )  cs

printClauses :: [Clause Name] -> String
printClauses  = printfClauses  id

printfImplClause :: (a -> Name) ->  ImplClause a -> String
printfImplClause pf ((a :-> b) :-> c)  = 
      "(" ++ pf a ++ " -> " ++  pf b ++ ") -> " ++ pf c

printImplClause :: ImplClause Name -> String
printImplClause = printfImplClause  id


printfImplClauses :: (a -> Name) ->  [ImplClause a] -> String
printfImplClauses pf ics =
  printfList (printfImplClause pf )  ics


printfImplClausesLn :: (a -> Name) ->  [ImplClause a] -> String
printfImplClausesLn pf ics =
  printfListSep "\n" (printfImplClause pf )  ics


-- pretty print formulas 

betweenParens :: String -> String
betweenParens f = "(" ++ f ++ ")"  


--printfForm :: (a -> Name) -> Form a -> String
printfForm :: Show a => (a -> Name) -> Form a -> String   -- DELETE !!!!
printfForm pf (Atom atm)  = pf atm

printfForm pf (f1 :&: f2) =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,AndOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,AndOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " & " ++  sf2'

printfForm pf (f1 :|: f2) =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,OrOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,OrOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " | " ++  sf2'


printfForm pf (f1 :=>: FALSE )  =
 let sf1 = printfForm pf f1
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
 in "~" ++  sf1'

printfForm pf (f1 :=>: Atom f2 ) | (pf f2) == false  =
 let sf1 = printfForm pf f1
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
 in "~" ++  sf1'

printfForm pf (f1 :=>: f2 )  =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " => " ++  sf2'

printfForm pf (f1 :<=>: f2 )  =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " <=> " ++  sf2'

printfForm pf f   = show f -- to remove!!!!
  

-- printfForms :: (a -> Name) -> [Form a] -> String
printfForms :: Show a  => (a -> Name) -> [Form a] -> String -- DELETE !!!
printfForms pf forms =
  printfList (printfForm pf ) forms


printfFormsLn :: Show a  => (a -> Name) -> [Form a] -> String 
printfFormsLn pf forms =
  printfListSep "\n"  (printfForm  pf ) forms


printCache ::  Cache -> String
printCache cache =
    let nameFormList =  cache_to_sortedNameFormList cache
        items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  nameFormList 
    in printfListSep "\n" id items

printCacheSubst ::  Cache  -> String
printCacheSubst cache   =
    let items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  (cache_to_nameFormSubstList cache)
    in printfListSep "\n" id items


cache_to_nameFormSubstList_withMainGoal ::  Cache ->  Form Name ->   [(Name, Form Name)]
--  list (name,form) such that  form is the formula equivalent to name
--  The input  formula is associated with mainGoalName (= "$goal")
cache_to_nameFormSubstList_withMainGoal  cache  inputForm   =
  let nameFormList = cache_to_sortedNameFormList cache
      subst =  Map.insert  mainGoalName inputForm    (Map.fromList  nameFormList) 
  in  map (\(name,form) ->  (name, (applySubst subst form)) ) nameFormList


printCacheSubst_withMainGoal ::  Cache  -> Form Name -> String
--  The input  formula is associated with mainGoalName (= "$goal")
printCacheSubst_withMainGoal cache  inputForm  =
    let nameFormList =  cache_to_nameFormSubstList_withMainGoal cache  inputForm
        items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  nameFormList
    in printfListSep "\n" id items

cache_to_subst_withMainGoal  :: Cache  -> Form Name  -> Substitution
-- substitution     extracted from the cache
--  The input  formula is associated with mainGoalName (= "$goal")
cache_to_subst_withMainGoal cache  inputForm   =
  Map.fromList $ cache_to_nameFormSubstList_withMainGoal cache inputForm 


-- ########## WORLDS

printfWorld :: Ord a => (a -> Name) ->  World a -> String
printfWorld f w =
  "W" ++  show ( worldIndex w) ++ " = "
  ++ printfAtmsBrace f (sort (worldAtms w) )

printfWorlds :: Ord a => (a -> Name) -> [World a] -> String
printfWorlds  f ws =
  printfListSep  " ;\n   "  (printfWorld f)  ws


printfModel ::  Ord a => (a -> Name) ->  Model a -> String
printfModel f mod = "<< " ++  printfWorlds f  (worlds mod)  ++ " >>"

isDigit :: Char -> Bool
isDigit c = (c >= '0') && (c <= '9' ) 

splitName :: Name -> (String,String)
-- split name and index:
-- p11 |-> (p,11) ,  p123q14 |-> (p123,14)  , pqr |-> (pqr, "")  
splitName atm =
  let atmRev = reverse atm
      (kRev, nameRev) = span isDigit atmRev 
  in
  (reverse nameRev, reverse kRev)  


-- ###

replaceWithInStr :: Char -> Char -> String -> String
-- replace a with b in tr
replaceWithInStr a b  = map (\c -> if c == a then b else c)




