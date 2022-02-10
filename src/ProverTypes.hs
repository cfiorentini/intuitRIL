{-# LANGUAGE TypeOperators #-}
module ProverTypes
 where


import qualified Data.Map as Map
import MiniSat  --  https://hackage.haskell.org/package/minisat


import Language
import Model

data Logic =
  Ipl  -- Intuitionistic Propositional Logic
  | Bd Int -- Bounded Depth  (bd n: depth at most n, with n >= 1)
  | GLn Int -- Goedel Logic n (gd n: linear + depth at most n, with n >= 1)
  | Dummett    
  | HereAndThere
  | Jankov
  | Kp


  deriving Eq

instance Show Logic where
  show  Ipl = "Ipl"
  show  (Bd n) = "Bd" ++ show n
  show  (GLn n) = "GL" ++ show n
  show  Dummett = "GL"
  show  HereAndThere = "Here and There"
  show  Jankov = "Jankov"
  show  Kp = "Kp"




-- ########  PROVER STATE ####

data SearchResult  = CountSat | Valid 
  deriving Eq
{-
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

-}

-- type Cache = Map.Map SimpleForm (Name, Bool, Bool)


-- cacheToMap :: Cache -> Map.Map Name (Form Name)
-- cacheToMap nameCache =
--     Map.fromList $ map ( \(sf, (name,_,_) ) -> ( name, simpleFormToForm sf) )  (Map.toList nameCache)

{-
cache_to_formNameList :: Cache -> [(Name, Form Name)]
cache_to_formNameList cache =
  map ( \(sf, (name,_,_) ) -> ( name, simpleFormToForm sf) )  (Map.toList cache)

-}


{-
printCache ::  Cache -> String
printCache cache =
  concatMap (\(name,form) ->   name ++ "  |--->  " ++ show form ++ "\n" )  ( cache_to_formNameList cache )
-}

-- constant fields 
data ProverEnv =
  ProverEnv{
     problemName :: String, -- the name of the problem
     logic :: Logic,
     inputFormula :: Form Name,
     initClauses :: [Clause Lit],  -- initial cs (flat clauses)
     initImplClauses :: [ImplClause Lit],  -- initial ics (implication clauses)
     initGoal ::  Lit, -- main goal
     initAtms ::  [Lit],  -- atoms in the input formula 
     -- countInitAtms :: Int,   -- count the atoms in (initClauses,initImplClauses,initGoal)
     traceLevel :: TraceLevel, -- trace level
     runDebugger ::  Bool -- print more info to debug
  }

mkProverEnv :: Logic -> String -> Form Name -> [Clause Lit] -> [ImplClause Lit] -> Lit -> [Lit] -> TraceLevel -> Bool -> ProverEnv
mkProverEnv logi problName inputForm cs ics goal univLits  traceLev debug =
   ProverEnv{
            problemName = problName,
            logic = logi,
            inputFormula = inputForm,
            initClauses = cs,
            initImplClauses = ics,
            initGoal =  goal,
            initAtms = univLits,
            traceLevel = traceLev,
            runDebugger = debug
            }

-- fields that can be updated 
data ProverState =
  ProverState{
     solver :: Solver,   -- the SAT-solver
     universe :: [Lit],   -- all literals occurring in the solver
     litToName_map ::  Map.Map Lit   Name ,  -- maps a Lit to the corresponding name (as atom)
     nameToLit_map ::  Map.Map Name  Lit ,   -- inverse map of litToName_map
     atmIndex :: Int, -- index to be used for the next new atom
     nameCache :: Cache, --  map simple formula |--> name (used in clausification)  
     -- substitution :: Substitution,  -- substitution name |--> formula
     countSat :: Int,    -- count the calls to the SAT-solver
     countRestBasic :: Int,    -- count the basic restarts
     countRestSem :: Int,      -- count the semantic restarts
     addedCsBasic :: [Clause Lit] ,  -- basic    cs  added to the  SAT-solver (learned clauses)  
     addedCsSem ::   [Clause Lit] ,      -- semantic cs  added to the  SAT-solver (derived from clausification of learned axioms)
     addedIcsSem ::  [ImplClause Lit] ,  -- semantic ics added to the  SAT-solver (derived from clausification of learned axioms)
     addedAxioms :: [Form Lit], -- learned axioms
     wIndex  ::  Int,  -- index of the next world
     model :: Model Lit,    -- model
     modelsSize :: [Int], -- list of the size (number of worlds)of the generated models (just before a restart)
     trace :: Trace Lit,  --  trace
     isValidForm :: Bool -- True iff the input formula is valid
  }

mkProverState :: Solver ->   [Lit] ->  Map.Map Lit  Name ->  Map.Map Name Lit -> Cache  -> Index -> ProverState
mkProverState sat univ ltToNm_map nmToLt_map cache index   =
   ProverState{
            solver = sat,
            universe = univ,
            litToName_map = ltToNm_map,
            nameToLit_map = nmToLt_map,
            nameCache = cache,
            atmIndex = index, 
            countSat = 0,
            countRestBasic = 0,
            countRestSem = 0,
            -- countNewAtms = 0,
            addedCsBasic = [],
            addedCsSem = [],
            addedIcsSem = [],
            addedAxioms = [],
            wIndex = 0,
            model = emptyModel,
            modelsSize = [],
            trace = emptyTrace,
            isValidForm = False
            }



--  Extract the function Lit -> Name from the map  litToName_map ::  Map.Map Lit Name in the prover state
litToName ::   ProverState -> Lit ->  Name
litToName  pst   = ( Map.! )  (litToName_map pst) 
 -- Map.! ::  Ord k => Map k a -> k -> a

   
--  Extract the function Name -> Lit from the map NameToLit_map ::  Map.Map Name Lit in the prover state
nameToLit ::   ProverState -> Name ->  Lit
nameToLit  pst  = (Map.!)  (nameToLit_map pst)  
 -- Map.! ::  Ord k => Map k a -> k -> a


     
initGoalName :: ProverEnv -> ProverState ->  GoalName 
initGoalName env pst =
   ltToNm $  initGoal env
   where
     ltToNm =  litToName pst   -- > Lit ->  Name

initClausesName ::  ProverEnv -> ProverState -> [Clause Name]
initClausesName env pst  =
  map (fmap ltToNm) (initClauses env)
  where
    ltToNm = litToName pst   -- > Lit ->  Name

initImplClausesName ::  ProverEnv -> ProverState ->  [ImplClause Name]
initImplClausesName env pst  =
  map (fmapImplClause ltToNm) (initImplClauses env)
  where
    ltToNm = litToName pst   -- > Lit ->  Name


addedCsBasicName :: ProverState ->  [Clause Name]
addedCsBasicName pst =
  map (fmap ltToNm ) (addedCsBasic pst) 
    where
    ltToNm = litToName pst   -- > Lit ->  Name

addedCsSemName :: ProverState ->  [Clause Name]
addedCsSemName pst =
  map (fmap ltToNm ) (addedCsSem pst) 
    where
    ltToNm = litToName pst   -- > Lit ->  Name

addedIcsSemName :: ProverState ->  [ImplClause Name]
addedIcsSemName pst =
  map (fmapImplClause ltToNm ) (addedIcsSem pst) 
    where
    ltToNm = litToName pst   -- > Lit ->  Name


countRest :: ProverState -> Int
countRest pst =
  countRestBasic pst + countRestSem pst


data ImplClauseType = Basic | Semantic
     deriving Eq

instance Show ImplClauseType  where
  show Basic = "basic"
  show Semantic = "semantic"


-- ##################   TRACE   ########################à

data TraceLevel =
  NoTrace
  | TraceLevel_low  -- only basic statistics (number of calls to SAT-solver, restarts) 
  | TraceLevel_medium -- also trace the size of generated models 
  | TraceLevel_high --  print all the traced information
  | TraceLevel_high_with_latex  -- also generate the tex files
   deriving ( Eq, Ord , Show)

data TraceStep a =
  Check(Int, ImplClause a )  
  | AskSatR(Int,Int, a )  
  | AskSatRW(Int,Int, Int,a,a )  
  | NewWorld(Int, [a])  
  | ProvedSat(Int,[a],a) 
  | NewBasicClause(Int,Int, Clause a)
  | NewSemClauses(Int,Int, Int,[Clause a],[ImplClause a],[Form a], Model a )
 
  
{-

Check(k, ic):  check the pair < world_k , impl > 
AskSatR(countSat,countRest, right ):    R_countRest |-- c right ?
AskSatRW(countSat,countRest, k , a, b ):  R_countRest, world_k, a |-- c b ?
NewWorld(k, atms):  generated a new world of index k containing atms
-- NewWorld(k, atms, omittedAtms ):  generated a new world of index k containing arms; the answer of the SAT-solver is NO(atms U omittedAtms)  
ProvedSat(countRest,assumps,right) --  R_countRest, assmups |--c  right
NewBasicClause(countSat,countRest, phi) --  phi is a new clauses   
NewSemClauses(countSat,countRest, chSize,semCs,semIcs,newAxiom,wrongModel)  --  new semantic cs, ics and new new axioms, model not respecting the semantic constraints 
-}

fmapTraceStep :: (Ord a, Ord b) => (a -> b) -> TraceStep a -> TraceStep b  
fmapTraceStep f (Check(k,ic)) = Check(k ,fmapImplClause f ic )
fmapTraceStep f (AskSatR(cntSat,cntRest,right)) = AskSatR (cntSat,cntRest, f right)
fmapTraceStep f (AskSatRW(cntSat,cntRest, wk,a, right)) = AskSatRW (cntSat,cntRest,wk,f a,  f right)
fmapTraceStep f (NewWorld (k, xs) ) = NewWorld( k, map f xs)
fmapTraceStep f (ProvedSat(k,xs,right)) = ProvedSat(k , map f xs , f right)
fmapTraceStep f ( NewBasicClause(cntSat, cntRest,c) ) = NewBasicClause(cntSat,cntRest, fmap f c)
fmapTraceStep f ( NewSemClauses(cntSat, cntRest, chSize,cs,ics,newAxioms,wrongModel) ) =
    NewSemClauses(cntSat,cntRest, chSize,map (fmap f) cs,  map (fmapImplClause f) ics,  map (fmap f) newAxioms, fmapModel f wrongModel)


{-
toSTring (Check(icType, k,ic)) = "Check"
toString  (AskSatR(cntSat,cntRest,right)) = "AskSatR" 
toString  (AskSatRW(cntSat,cntRest, wk,a, right)) =  "AskSatRW"
toString (NewWorld (k, xs) ) =  "NewWorld"
toString (ProvedSat(k,xs,right)) = "ProvedSat"
toString ( NewBasicClause(cntSat, cntRest,c) ) = "NewBasicClause"
toString ( NewSemClauses(cntSat, cntRest,cs,ics,newAxioms,wrongModel) ) = "NewSemClauses"
-}



traceName :: ProverState -> Trace Name
traceName pst = fmapTrace ltToNm (trace pst) 
  where  ltToNm = litToName pst

data Trace a = Trace [TraceStep a]


fmapTrace ::  (Ord a ,Ord b) => (a -> b) -> (Trace a -> Trace b)  
fmapTrace f (Trace steps) = Trace( map (fmapTraceStep f) steps )

emptyTrace :: Trace a  
emptyTrace = Trace []

addStep :: TraceStep a ->   Trace a -> Trace a
addStep step (Trace steps) = Trace (step: steps) 

addSteps :: [TraceStep a] ->   Trace a -> Trace a
addSteps [] tr = tr
addSteps (s1 :steps) tr =
  addStep s1  (addSteps steps tr)

getSteps :: Trace a -> [TraceStep a]
getSteps (Trace steps) = reverse steps

