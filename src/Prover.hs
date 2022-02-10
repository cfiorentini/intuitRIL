{-# LANGUAGE TypeOperators #-}
module Prover (
  proveProblem  -- Logic -> TraceLevel -> FilePath -> Cache  -> Index -> Form Name -> [Clause Name] -> [ImplClause Name] -> Name -> Bool -> IO ()
                -- prover with trace and derivations/countermodels
)
  where

-- import Data.IORef
import System.IO
import qualified Data.Map as Map
-- import Data.Maybe
import Data.List
import Data.Char
import System.Directory
import System.FilePath
import Control.Monad.State
import Control.Monad.RWS
import MiniSat  --  https://hackage.haskell.org/package/minisat

import Clausify
import Language 
import Model
import ProverTypes
import Utility
import WriteLatex
import WriteModelGraphviz
import WriteMakeFile

-- IMPLEMENTED LOGICS
import qualified BoundedDepth as BoundedDepth
import qualified Dummett as Dummett
import qualified DummettBoundedDepth as DummettBoundedDept
-- import qualified HereAndThere as HereAndThere
import qualified Jankov as  Jankov
import qualified Kp as  Kp

-- Type Lit represents the literals of the SAT-solver language


-- ################################################################
-- #######        PROVER  WITH  TRACE                      ########
-- ################################################################



-- newtype RWST r w s (m :: * -> *) a
-- A monad transformer adding reading an environment of type r, collecting an output of type w and updating a state of type s to an inner monad m.
-- The Writer w is not used 


-- ProverConf :: * -> *
type ProverConf = RWST ProverEnv () ProverState IO


proveProblem :: Logic -> TraceLevel -> FilePath -> Cache  -> Index -> Form Name -> [Clause Name] -> [ImplClause Name] -> Name -> Bool -> IO ()
-- (cs,ics,goal): problem to solve in clausal form
-- ASSUMPTION:  (closureImplClauses ics) \subseteq cs
proveProblem logi traceLev file nameCache formIndex inputForm cs ics goal debug  = 
 do
  let baseName = takeBaseName file
  (proverEnv,initialProverState)  <- initProver logi traceLev baseName nameCache  formIndex inputForm cs ics goal debug
  ( res,finalProverState, _) <-  runRWST  runMainLoop  proverEnv  initialProverState
  case res of
       Valid  ->  -- valid problem
         do
           putStrLn ( writeStatistics proverEnv finalProverState )
           when (countRest finalProverState > 0 &&  traceLev >= TraceLevel_medium )(
             putStrLn $ "Size (number of worlds) of the generated models: "
                 ++ (show . reverse . modelsSize) finalProverState
            ) -- end when
           putStrLn $ "+++ RESULT: Valid (Logic " ++ show logi  ++ ")"  
           when (traceLev >= TraceLevel_high_with_latex) (writeOutputFiles proverEnv finalProverState)
       CountSat ->
         do
           putStrLn ( writeStatistics proverEnv finalProverState )
           when ( traceLev >= TraceLevel_medium )(
             putStrLn $ "Size (number of worlds) of the generated models: "
                 ++ (show . reverse . modelsSize) finalProverState
            ) -- end when
           putStrLn $ "+++ RESULT: Not Valid (Logic " ++ show logi ++ ")"  
           when (traceLev >= TraceLevel_high_with_latex) (writeOutputFiles proverEnv finalProverState)
                   
            
writeOutputFiles ::  ProverEnv -> ProverState -> IO ()
writeOutputFiles proverEnv finalProverState =
  do
    let problName = problemName proverEnv
        isValidProblemFormula = isValidForm  finalProverState
        ltToNm = litToName finalProverState 
        logiWithoutSpaces =  map toUpper $ replaceWithInStr ' ' '_' $ (show . logic) proverEnv
        traceName =  "trace_"  ++ problName   ++ "_" ++ logiWithoutSpaces
        derName= "derivation_"  ++ problName  ++ "_" ++ logiWithoutSpaces
        modelName= "countermodel_"  ++ problName ++  "_" ++ logiWithoutSpaces
        dirName = "out-" ++ problName ++ "-" ++ logiWithoutSpaces
        texTraceFile = combine dirName (addExtension traceName ".tex")
        -- texDerFile = combine dirName (addExtension derName ".tex")
        gvFileName baseName =  combine dirName (addExtension baseName ".gv")
        counterModel =  fmapModel ltToNm  ( model finalProverState )
        makeFile = combine dirName  "Makefile"
        msgMake = (concat $ replicate 80 "*" ) ++
                 "\n---> Output files are in the directory '" ++    dirName  ++ "'" ++
                 "\n---> Move into directory '" ++ dirName ++ "' and run command 'make' to compile them"
        (latexTrace,wrongNamesModels) =  writeLatexTrace proverEnv finalProverState
        -- wrongNModels :: [(String,Model Name)] 
        (wrongNames,_) = unzip wrongNamesModels 
        -- gvFilesWrongModels = map ( name -> combine dirName (addExtension name ".gv")) wrongModels
    createDirectoryIfMissing True dirName             
    writeFile texTraceFile latexTrace
    mapM_ (\ (name,mod)  ->   writeFile (gvFileName name)  (writeModelGraphviz name mod)) wrongNamesModels
    if isValidProblemFormula then
      do
        -- writeFile texDerFile (writeLatexDerivation  proverEnv finalProverState )
        writeFile makeFile   (writeMakeFile Valid traceName derName wrongNames)
    else -- the problem formula is not valis
      do
        writeFile (gvFileName modelName)  (writeModelGraphviz problName counterModel )
        writeFile makeFile (writeMakeFile CountSat  traceName modelName wrongNames)
    putStrLn msgMake


initProver :: Logic -> TraceLevel -> FilePath -> Cache -> Index -> Form Name -> [Clause Name] -> [ImplClause Name] -> Name ->  Bool -> IO (ProverEnv,ProverState)
initProver logi traceLev file nameCache  formIndex inputForm cs ics goal debug =
  do
  let names = getNames cs ics goal
  sat <- newSolver
  -- create the literals (in the SAT-solver language), one for each  name occurring in the input formulas
  univLits <- sequence [ newLit sat | _ <- names ] -- universe  :: [Lit]
  -- create maps to encode/decode formulas 
  let nmToLt_map  = Map.fromList (names `zip` univLits)  -- Name to Lit map
      nmToLt =  (Map.!) nmToLt_map  -- Name -> Lit
      -- Map.! ::  Ord k => Map k a -> k -> a
      ltToNm_map = Map.fromList (univLits `zip` names)  -- Lit to Name map
  addClause sat [ neg  (nmToLt false)  ]  -- add "not false" to the sat solver 
-- translate cs and ics into the SAT-solver language
  let csLit =  map (fmap nmToLt) cs
      icsLit = map (fmapImplClause nmToLt) ics
      initLits = map nmToLt  (getFormNames inputForm)
  -- add  clauses to sat
  sequence_
    [ addClause sat (map neg xs ++  ys) | (xs :=> ys) <- csLit ]
    {- for every clause
            [x1, ..  xm] :=> [y1 .. yn]
       // representing the formula (x1 & .. & xm) => (y1 | ... | yn)  
       in csLit add the clause
         ~x1 | ... |~xm | y1 | ... | yn
       to the SAT-solver  
   -}
  -- proving
  simplify sat
  let proverEnv =  mkProverEnv logi file  inputForm csLit icsLit  (nmToLt goal) initLits traceLev debug
      initialProverState =  mkProverState sat univLits  ltToNm_map nmToLt_map  nameCache  formIndex
  return  (proverEnv, initialProverState) 


runMainLoop ::  ProverConf SearchResult 
-- init main loop 
-- In (S3), the new world is added to the empty model (thus, STEP (S1) is skipped) ?????
runMainLoop  =
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        goal =   initGoal env
        ltToNm = litToName pst
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel env
        step_askSatR = AskSatR(cntSat,cntRest, goal)
    when( traceLev >= TraceLevel_high )(    
       liftIO $ putStrLn $ printStep (cntSat + 1) ++ printfAsk ltToNm  Nothing cntRest goal
       ) -- end when
    -- @SAT:  SAT |-- goal ?     
    isSat <- lift $ solve sat [neg goal]  --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 }  )
    when( traceLev >= TraceLevel_high )(
       modify ( \ s -> s{trace = addStep step_askSatR  (trace s) } ) )
    if isSat then
     --  SAT |-- goal    ====>    NO(M)
     --  M is a model of SAT  such that goal \not\in M 
     -- trueAtoms = atoms in M
     do
         trueAtms <- lift $ trueAtmsInSat sat (universe pst) 
         let wkInd = wIndex pst -- index of the new world
             wkAtms =   trueAtms 
             newWorld = mkWorld wkInd   wkAtms
             newModel = addWorld newWorld emptyModel
             step_foundW = NewWorld(wkInd,wkAtms)
             icsBasic = initImplClauses env
             icsSem = addedIcsSem pst
             newWorldRec = mkWorldRec newWorld (filterIcsToCheck newWorld (icsBasic ++ icsSem) )   
         modify ( \ s -> s{wIndex = wkInd + 1 , model = newModel} )
         ( when( traceLev >= TraceLevel_high ) $
             do
               modify ( \s -> s{trace = addStep step_foundW (trace s) } )
               liftIO $  putStrLn  $ ">>> NO( " ++ printfAtmsBrace ltToNm trueAtms ++ " )"
               liftIO $ putStrLn $ printfNewWorld ltToNm cntSat newWorld 
               liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel 
           ) -- end when
         innerLoop_ics  $ mkWorldRecs newWorldRec  --  continue inner loop to check the  ics
         else
      --  SAT |-- goal  ===>  es({})
      --  SAT |-- goal and (cs,ics,goal) is Valid
        do
          -- update prover state
          modify ( \ s -> s{isValidForm = True  }  )
          let  step_valid =  ProvedSat(cntRest,[], goal )
          when( traceLev >= TraceLevel_medium )(
              modify( \ s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
             ) -- end when
          ( when( traceLev >= TraceLevel_high ) $
            do
              liftIO $ putStrLn $ ">>> YES( {} )"    
              modify ( \ s -> s{trace = addStep step_valid (trace s)} )
           ) -- end when
          return Valid


-- ###############   LOOPS IMPLEMENTATION  ##########################

{- 
 
An implication clause (a=>b)=>c is *checked* (or *realized*)  in a world w iff one of the following conditions hold:

C1)  ( w |-- a  or  w |-- b or   w |-- c )  *OR*
C2)  there is w' (in the current model) such that w < w' and w |-- a  or  w |-/- b 

A  worldRec  stores the information about the implication clauses checked or to be checked 


-}

data WorldRec =
  WorldRec{
     world ::  World Lit,         -- world w
     toCheck ::      [ImplClause Lit],     -- basic    ics not satisfying (C1),  (C2) must be be checked
     checked ::      [ImplClause Lit]      -- checked  (all ics satisfy (C2))
     } -- deriving Show

-- *ASSUMPTION*:  toCheck is not empty


-- A worldRecs collects all the worldRec's containing at least one ic to be checked XXXX DELETE


{-
data WorldRecs  =
  WorldRecs {
    wRecsOnlyBasic ::           [ WorldRec ] ,        -- wRecs only containing basic ics to be checked
    wRecsAtLeastOneSemantic ::  [ WorldRec ]         --  wRecs containing at least one semantic ic to checked
  } -- deriving Show
-}

{-

We maintain a list of wRec, storing the ics to be checked

Let wRec be the first record of the wRec  list

We check the firs ic in the list toCheck of wRec

  
-}

mkWorldRec :: World Lit  -> [ImplClause Lit]   -> WorldRec 
-- make a new WorlRec with the provided basic and semantic ics to be checked 
mkWorldRec w icsToCheck  =
  WorldRec{world =  w , toCheck = icsToCheck , checked = []  } 

{-
emptyToCheck :: ImplClauseType ->  WorldRec  -> Bool
-- check the toCheck lists
emptyToCheck Basic    wRec    = null $ toCheck wRec 
emptyToCheck Semantic wRec    = null $ toCheckSemantic wRec
-}

filterIcsToCheck :: World Lit -> [ImplClause Lit] ->  [ImplClause Lit]
-- given a world w and a list ics, filter the ic of ics not satisfying condition (C1)
-- (namely, the ic such that (C2) must be checked)
filterIcsToCheck w ics =
    [ ic | ic@((a:->b):->c) <- ics, w .|-/-. a ,   w .|-/-. b ,   w .|-/-. c  ]


updateWorldRecs ::  [WorldRec]  -> [WorldRec]
-- The first ic of the first worldRec has been checkd.
-- Update worldRec list  for next iteration
updateWorldRecs (wRec : wRecs) =
  let ( icChecked : ics ) = toCheck wRec
  in
  if null ics then
      wRecs -- no more ics to check in wRec, wRec is discarded
  else
     let newWRec = wRec{ toCheck  = ics, checked = icChecked : (checked wRec) }
     in  newWRec : wRecs  -- icChecked has been moved in the checked list

mkWorldRecs :: WorldRec  ->  [WorldRec]
-- make a list containing a wRec
-- if wRec has no ics to check, the list is empty
mkWorldRecs wRec =
  if (null .toCheck) wRec then [] else [wRec]

addWorldRec ::  WorldRec  -> [WorldRec] -> [WorldRec]
-- if wRec has ics to check, add wRec to wordRecs,
-- otherwise the list is not updated
addWorldRec wRec worldRecs =   
  if (null .toCheck) wRec then  worldRecs else wRec : worldRecs


---------------------

innerLoop_ics ::   [WorldRec]   -> ProverConf SearchResult 
-- Start inner loop  

innerLoop_ics  []  =
  -- no more ics to check
  -- check if the model respects the semantic constraints
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    -- liftIO $ putStrLn  $ ">>>>>>>" ++  ( printfAtmsBrace (litToName pst) (initAtms env) )-- XXXX
    let newAxioms = checkModel (logic env) (model pst)  (initAtms env)
    if ( (not . null) newAxioms  ) then
       --  newAxioms is not empty since the model does not respect the semantic constraints 
       --  Clausify newAxioms, add the new clauses to the SAT-solver and restart 
       do
         when( traceLevel env >= TraceLevel_high )(
               liftIO $ putStrLn  "!!!! The semantic constraints have been violated !!!!"
             )
         addNewSemClauses_and_restart newAxioms
    else -- the model respects the semantics, countermodel found 
       do
         when( traceLevel env >= TraceLevel_medium )(
                modify( \s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
                ) -- end when
         return CountSat
  
innerLoop_ics  worldRecs  =
-- at leas an ic to check
  do
    env <- ask  -- get prover environment
    pst0 <- get  -- get prover state
    ( when ( runDebugger env ) $
       do
         liftIO $ putStrLn $ startDebug  "INNER LOOOP ICS" 
         liftIO $ putStrLn $ printfWorldRecs (litToName pst0) worldRecs 
         liftIO $ putStrLn $ endDebug
      ) -- end when
    -- liftIO $ putStrLn "++ BEGIN #########################################"    --  XXXX
    -- liftIO $ putStrLn $ printfWorldRecs (litToName pst) worldRecs   --  XXX
    -- liftIO $ putStrLn "++ END #########################################"    --  XXXXX
   -- We check the first ic = (a:->b):->c  in worldRecs of type icType
    let sat = solver pst0
        cntSat =  countSat pst0
        cntRest = countRest pst0
        ltToNm = litToName pst0
        traceLev = traceLevel env
        wRec = head worldRecs 
        w = world wRec
        (a:->b):->c   =  ( head. toCheck )  wRec
    ( when ( runDebugger env ) $
       do
        liftIO $ putStrLn $ startDebug  "WORLD REC TO CHECK" 
        liftIO $ putStrLn $ printfWorldRec ltToNm wRec       
        liftIO $ putStrLn $ endDebug
        ) -- end when
    if (model pst0,w)  .|=/=.  (a :-> b)    then
    --  In the current model  (model pst0), there is a world w' such that w < w' and  w'|-- a and  w'|-/- b
    --  thus (a:->b):->c > satisfies (C2) and is set as checked 
        innerLoop_ics  $ updateWorldRecs  worldRecs -- continue the loop with the updated worldRecs
    else
    --  select the pair < w,  (a:->b):->c >  
    --  try to add a new world w' such that w < w' and   w'|-- a and  w'|-/- b
     do
      let step_selected = Check(worldIndex w, (a:->b):->c )
      ( when( traceLev >= TraceLevel_high ) $
        do
        -- update prover state
           modify  ( \ s ->s{ trace = addStep  step_selected  (trace s) } )
           liftIO $ putStrLn ( printStep cntSat  ++  "Selected: < " ++
              printW  (worldIndex w)  ++ ", " ++  printfImplClause ltToNm  ((a:->b):->c)  ++ " >" )
           liftIO $ putStrLn $ "========================================"   
           liftIO $ putStrLn (printStep (cntSat + 1) ++
                printfAsk ltToNm ( Just ( (a:->b):->c  , worldIndex w))  cntRest b  )
       ) -- end when
      innerLoop_satProve  worldRecs   (w, (a:->b):->c , wRec )  



innerLoop_satProve :: [WorldRec] ->  (World Lit,ImplClause Lit,WorldRec) -> ProverConf SearchResult 
innerLoop_satProve  worldRecs  (w,  (a:->b):->c ,wRec)  =
-- run inner loop from step (S7)
--  < w, (a:->b):->c > is the pair selected in (S4), wRec the world record of w
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let logi = logic env
        sat = solver pst
        mod = model pst  
        ltToNm = litToName pst
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel env
        step_askRW =  AskSatRW(cntSat,cntRest,  worldIndex w, a, b)
    -- @SAT:  SAT, w , a |-- b ?     
    isSat <- lift $ solve sat ( neg b : a : worldAtms w ) --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 })
    when( traceLev >= TraceLevel_high )(
       modify (  \ s -> s {trace = addStep step_askRW (trace s) } )
       ) -- end when 
    if isSat then
    -- SAT, w , a |-- b  ====>    No(M)
    -- M is a model of 'SAT \cup w \cup {a}' such that b \not\in M
    -- M generates a new world
    -- trueAtoms = atoms in M
       do
         trueAtms <- lift $ trueAtmsInSat sat (universe pst)
         let wkInd = wIndex pst -- index of the new world
             wkAtms =   trueAtms 
             newWorld = mkWorld wkInd wkAtms  
             step_foundW = NewWorld(wkInd,wkAtms)
         ( when( traceLev >= TraceLevel_high ) $
           do
             -- update prover state
             modify ( \ s -> s{trace = addStep step_foundW (trace s) } )
             liftIO $ putStrLn $ ">>> NO( " ++ printfAtmsBrace ltToNm trueAtms ++ " )" 
             liftIO $ putStrLn $ printfNewWorld ltToNm cntSat newWorld  
             ) -- end when
          -- the ics to be checked for the new world are *all* the ics selected to be checked when w has been created  
         let allIcs = toCheck wRec  ++ checked wRec
             icsToCheck    =   filterIcsToCheck newWorld allIcs 
             newWRec =  mkWorldRec newWorld icsToCheck     
             newModel = addWorld newWorld (model pst)
         -- update prover state
         modify ( \ s -> s{wIndex = wkInd + 1, model = newModel}  )
         when( traceLev >= TraceLevel_high )(
                 liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel
              ) -- end when
          -- (a:->b) :-> c has been checked, new iteration of the inner loop
         -- liftIO $ putStrLn " BEGIN #########################################"    --  XXXX
         -- liftIO $ putStrLn $ printfWorldRecs (litToName pst)  (updateWorldRecs icType worldRecs)   --  XXX
         -- liftIO $ putStrLn "END #########################################"    --  XXXXX
         innerLoop_ics $  addWorldRec newWRec  ( updateWorldRecs worldRecs ) 
    else
       -- SAT, w , a |-- b :   Yes(assumps) ,  where assumps \subseteq ( w U {a} )
       -- thus  SAT, assumps |-- b 
       do
       -- compute assumps
        xs <- lift $ conflict sat   -- conflict :: Solver -> IO [Lit] 
        -- Let xs = x1, ... , xn, then:
        -- SAT |--   x1 | ... | xn and b is an element of xs
        let assumps =  map neg ( xs \\ [b] )
             -- assumps = ~x such that x \in xs and x /= b
            newClause = [ x | x <- assumps, x /= a  ] :=> [ c]
            step_proved =  ProvedSat(cntRest,  assumps, b )
        ( when( traceLev >= TraceLevel_high ) $
           do
            -- update prover state  
            modify ( \ s -> s{trace = addStep step_proved (trace s)  }) 
            liftIO $ putStrLn $ ">>> YES( " ++  printfAtmsBrace ltToNm assumps   ++    " )"       
          ) -- end when
        addNewBasicClause_and_restart newClause

    



-- #############################################################à



addNewBasicClause_and_restart :: Clause Lit  -> ProverConf  SearchResult 
addNewBasicClause_and_restart newClause   =
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        cntSat =  countSat pst
        cntRest = countRest pst
        ltToNm = litToName pst
        traceLev = traceLevel env
        step_newc = NewBasicClause(cntSat, cntRest,newClause)
    lift $ satAddClause sat  newClause 
            -- update prover state
    modify( \ s -> s{
              countRestBasic = countRestBasic s + 1,
              addedCsBasic =  newClause : addedCsBasic s,
              modelsSize =  sizeModel (model s) : (modelsSize s)
             })
    ( when( traceLev >= TraceLevel_high ) $
      do
         -- update prover state
         modify  ( \ s -> s{trace = addStep step_newc (trace s) } )  
         liftIO $ putStrLn  $ printStep cntSat ++  "New clause (basic):\n" ++  printfClause ltToNm newClause 
         liftIO $ putStrLn ( printStep cntSat ++   printR   (cntRest + 1) ++ " = " ++ printR cntRest ++ " +  new clause" )                   
         liftIO $ putStrLn ( "###########  RESTART " ++ show (cntRest + 1)  ++ " (BASIC)" ++
                           "  ###########" )
      )-- end when
    runMainLoop  -- ## RESTART


addNewSemClauses_and_restart :: [Form Lit]  ->   ProverConf  SearchResult 
addNewSemClauses_and_restart newAxioms =
  do
    env <- ask  -- get prover environment
    (newCs,newIcs) <- clausifyNewAxioms  newAxioms  -- NOTE: clausifyNewAxioms modifies the prover state!
    pst <- get  -- get prover state
    let sat = solver pst
        cntSat =  countSat pst
        cntRest = countRest pst
        ltToNm = litToName pst
        traceLev = traceLevel env
        cache = nameCache pst
        chSize = cacheSize cache
        step_newSemClauses = NewSemClauses(cntSat, cntRest,chSize,newCs,newIcs,newAxioms,model pst)
    lift $ satAddClauses sat newCs
     -- update prover state
    modify( \ s -> s{
              countRestSem = countRestSem pst  + 1,
              addedCsSem =  newCs  ++ addedCsSem s,
              addedIcsSem = newIcs ++ addedIcsSem s,
              addedAxioms = newAxioms ++ (addedAxioms s),
              modelsSize =  sizeModel (model s) : (modelsSize s)
             })
    ( when( traceLev >= TraceLevel_high ) $
      do
        let subst = Map.fromList $ cache_to_nameFormSubstList_withMainGoal cache  (inputFormula env)
            newAxiomsName =  map (fmap ltToNm) newAxioms 
            newAxiomsSubst = map (applySubst subst)  newAxiomsName
       -- update prover state
        modify  ( \ s -> s{trace = addStep step_newSemClauses (trace s) } )
        liftIO $ putStrLn  $ printStep cntSat ++  "New axioms:\n" ++  printfForms id newAxiomsName  
        liftIO $ putStrLn  $ printStep cntSat ++  "New semantic clauses:\n" ++  printfClauses ltToNm newCs  
        liftIO $ putStr    $ printStep cntSat ++
          ( if null newIcs then "" else  "New semantic impl. clauses:\n" ++  printfImplClauses ltToNm newIcs ++ "\n")
        liftIO $ putStrLn ( printStep cntSat ++   printR   (cntRest + 1) ++ " = "
            ++ printR cntRest ++ " + new semantic clauses"  )
        liftIO $ putStrLn  $ "Internal map:\n" ++  printCache cache
        liftIO $ putStrLn  $ "Name Map:\n" ++  printCacheSubst_withMainGoal cache  (inputFormula env)
        liftIO $ putStrLn  $ "New Axioms  (with substitution):\n" ++   printfForms id newAxiomsSubst 
        liftIO $ putStrLn ( "###########  RESTART " ++ show (cntRest + 1)  ++ " (SEMANTIC)" ++
                              "  ###########" )
       )-- end when
    runMainLoop  -- ## RESTART

     


checkModel :: Logic ->   Model Lit -> [Lit] ->   [Form Lit]
{-
  Let logi be the  logic at hand  and mod  the current model.
  Check if mod respect the semantic constraints of the logic
  - If mod is does not respect the semantic constraints, return the new axioms to be added
  - If mod respects the constraint, return the empty list
 
inputAtms are the literal correspondings to the atoms in the input formula

 For each logic, we have to implement a function

   checkModel :: Ord a =>   Model a ->   [Form a]


-}

checkModel logi mod inputAtms =  
   case logi  of
      Ipl            ->  []   -- no semantic constraints
      Bd n           ->  BoundedDepth.checkModel  mod n
      Dummett        ->  Dummett.checkModel  mod  inputAtms
      GLn n           -> DummettBoundedDept.checkModel mod n inputAtms
      -- HereAndThere   ->  HereAndThere.checkModel  mod inputAtms 
      Jankov         ->  Jankov.checkModel  mod inputAtms 
      Kp             ->  Kp.checkModel  mod inputAtms 



clausifyNewAxioms :: [Form Lit] ->   ProverConf   ([Clause Lit],[ImplClause Lit])
-- Clausification of semantic axioms
-- Note that new atoms can be created
clausifyNewAxioms  newAxioms =
  do
    pst <- get  -- get prover state
    let  sat = solver pst
         cache = nameCache pst
         index = atmIndex pst
         ltToNm_map = litToName_map pst
         nmToLt_map = nameToLit_map pst 
         ltToNm = litToName pst
         newAxioms_name = map (fmap ltToNm ) newAxioms
         (newCache, newIndex,cs1_name,ics_name ) =  clausifyForms index newAxioms_name
         cs2_name = closureImplClauses ics_name 
         cs_name = cs1_name `union` cs2_name
    -- liftIO $ putStrLn  $ ">>>>>>>>>>>\n" ++  printCache newCache ++ "\n<<<<<<<<<<<<<<<<<"
    -- liftIO $ putStrLn  $ ">>>>>>>>>>>\n" ++  printCache (  cache   `Map.union` newCache) ++ "\n<<<<<<<<<<<<<<<<<"   
    newLits <- liftIO $   mapM (\_ -> newLit sat) [ index .. newIndex - 1 ]
    let newNames = map mkNewName [index .. newIndex - 1 ]
        new_nmToLt_map =  nmToLt_map `Map.union` Map.fromList (newNames `zip` newLits)   -- update Name to Lit map
        new_ltToNm_map =  ltToNm_map `Map.union` Map.fromList (newLits  `zip` newNames)  -- update Lit to Name map
    modify( \s ->  s{
              universe = newLits ++ universe s,
              litToName_map = new_ltToNm_map,
              nameToLit_map = new_nmToLt_map,
              nameCache = cache   `Map.union` newCache,
              atmIndex = newIndex
              }
          )
    let  new_nmToLt = (Map.!) new_nmToLt_map  -- Name -> Lit
         cs_lit  = map (fmap new_nmToLt ) cs_name
         ics_lit = map (fmapImplClause new_nmToLt ) ics_name
    return ( cs_lit ,  ics_lit  )

 -- Map.! ::  Ord k => Map k a -> k -> a





-- #############################################################à

writeStatistics :: ProverEnv -> ProverState -> String
writeStatistics env pst =
  let sizeCounterModel =
        if (isValidForm pst) then "" else
          "\nWorlds in the countermodel: " ++ show ( sizeModel (model pst) )
      ltToNm_map = litToName_map  pst
      ltToNm = litToName  pst
      addedAxs =  map (fmap ltToNm)  (addedAxioms  pst)
      cache = nameCache pst
      subst = Map.fromList $ cache_to_nameFormSubstList_withMainGoal cache  (inputFormula env)
      addedAxsSubst = map (applySubst subst)  addedAxs
      traceLev = traceLevel env
      strLearnedAxioms_and_map =
        "\nLearned axioms (possibly with new variables): "  ++  show (length (addedAxioms  pst)) ++ "\n" 
        ++  printfFormsLn  (ltToNm_map  Map.!)   (addedAxioms  pst)  --  unlines ( map show  (addedAxioms  pst) )
        ++ sizeCounterModel
        ++  "\nInternal Cache:\n" ++ printCache cache
        ++  "\nName Map:\n" ++ printCacheSubst_withMainGoal cache  (inputFormula env)
      countInitCs =    (length  . initClauses ) env
      countAddedCsBasic =   (length  . addedCsBasic ) pst
      countAddedCsSem =     (length  . addedCsSem ) pst
      countTotCs =  countInitCs +  countAddedCsBasic + countAddedCsSem
      countInitIcs =    (length  . initImplClauses ) env
      countAddedIcsSem =     (length  . addedIcsSem ) pst
      countTotIcs =  countInitIcs +  countAddedIcsSem
      --  countInitAtms = (length . initAtms) env
      -- countAddedAtms =  atmIndex pst
      -- countTotAtms = countInitAtms + countAddedAtms
      -- countAddedAtms = 
  in 
  -- 
  -- ++ "\nImpl. clauses: " ++ show ( length (initImplClauses env) )
  -- ++ "\nAtoms: " ++ show ( length (universe pst) )
  "Calls to the SAT-solver: " ++ show ( countSat pst ) 
  ++ "\nRestarts: " ++  show (countRest pst)
  ++ " (" ++ show (countRestBasic pst) ++  " basic, " ++  show (countRestSem pst) ++ " semantic)"
  -- ++ "\n*** TRACE LEVEL " ++ show traceLev
  ++ ( if ( traceLev >= TraceLevel_high ) then  strLearnedAxioms_and_map  else "" )
  ++ "\nAdded clauses: " ++ show countTotCs ++ " ("
  ++  show countInitCs ++ " initial, " ++  show countAddedCsBasic ++ " basic rest., " ++  show countAddedCsSem ++ " sem. rest.)"
  ++ "\nAdded impl. clauses: " ++ show countTotIcs ++ " ("
  ++  show countInitIcs ++ " initial, " ++  show countAddedIcsSem ++ " sem. rest.)"
  -- ++ "\nNew atoms: " ++ show countTotAtms ++ " ("
  -- ++ show countInitAtms ++ " after initial clausification, " ++ show countAddedAtms ++  " added in sem. restarts)"
  ++ "\nLearned axioms: "  ++  ( show .length ) addedAxs  ++ "\n" 
  ++  printfFormsLn id addedAxsSubst 
  -- Map.! ::  Ord k => Map k a -> k -> a

printfAsk :: (Lit -> Name) -> Maybe(ImplClause Lit,Int) -> Int -> Lit -> String
printfAsk   ltToNm appliedRule cntRest right  =
  let left = case appliedRule of
        Nothing -> ""
        Just((a :-> b) :->c ,k ) -> ", " ++ printW k ++ ", " ++ ltToNm a
  in
  "@SAT: " ++ printR  cntRest  ++  left ++ " |-- " ++ ltToNm right ++ " ?" 
 
printW :: Int -> String
printW k = "W" ++ show k

printR :: Int -> String
printR k = "R" ++ show k



printStep :: Int -> String
printStep k = "[" ++ show k ++ "] "

printfAddedWorld ::  Ord a => (a -> Name) ->  Int -> World a -> Model a -> String
printfAddedWorld ltToNm cntSat newW newM =
         printStep (cntSat  + 1 ) ++  "Added new world\n"
         ++ printStep (cntSat + 1 ) ++  "Current model:\n" 
         ++ printfModel ltToNm newM

printfNewWorld ::  Ord a => (a -> Name) ->  Int -> World a -> String
printfNewWorld ltToNm cntSat newW  =
         printStep (cntSat  + 1 ) ++  "New world:\n" 
         ++ printfWorld ltToNm newW



------------------
-- debug
printfWorldRec  ::   (Lit -> Name)  -> WorldRec -> String
printfWorldRec ltToNm wRec =
  "\n" ++ printfWorld ltToNm (world wRec) 
  ++ "\n---ToCheck: " ++ printfImplClauses ltToNm (toCheck wRec)
  ++ "\n---Checked: " ++ printfImplClauses ltToNm (checked wRec)



printfWorldRecs  ::   (Lit -> Name)  -> [WorldRec] -> String
printfWorldRecs ltToNm worldRecs =
  "################################################"
   ++ concatMap   (printfWorldRec ltToNm)  worldRecs
 



startDebug :: String -> String
startDebug msg = ">>>>>> " ++ msg ++ " <<<<<<"


endDebug ::  String
endDebug = ">>>>>><<<<<<"


-- ############################   TEST
{-
testClausify :: [Form Name] -> IO ()
testClausify fs =
  do
    let (index,cache, cs, ics) = clausifyForms 5 fs
    putStrLn  $ "=== CLAUSES ===\n" ++  printfClauses id cs 
    putStrLn  $ "=== IMPL. CLAUSES ===\n" ++  printfImplClauses id ics 
    putStrLn  $ "=== CACHE ===\n" ++  printCache cache
    putStrLn  $ "=== NAME MAP ===\n" ++  printCacheSubst cache


a = Atom "a"
b = Atom "b"
c = Atom "c"
kp = ( negf a :=>: b :|: c) :=>:  ( negf a :=>: b ) :|:  ( negf a :=>: c )
-}
