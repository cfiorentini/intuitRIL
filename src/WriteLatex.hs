{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}



module  WriteLatex
  (
     writeLatexTrace,           --   ProverEnv -> ProverState  -> (String,[(String,Model Name)])
     -- return (strTrace,wrongModels) where:
     --   strTrace:   string representing the trace
     -- wrongModels:  list  (name,wrongModel) of models not satisfying the semantic constraints
     writeLatexDerivation       --   ProverEnv -> ProverState  -> String
  )


where

import Text.RawString.QQ
import Data.List
import Data.Maybe
import Control.Monad.State
import qualified Data.Map as Map


import Language
import Model
import ProverTypes
import Utility


data Context =  Context {
  cntGoal :: Name,            -- main goal
  cntInitCs :: [Clause Name],      --  initial clauses    
  cntAddedCsBasic ::  [Clause Name],  -- added clauses (learned clauses)
  cntAddedCsSem   ::  [Clause Name],   -- semantic added clauses (learned clauses) 
  cntInitIcs :: [ImplClause Name],   -- initial implication clauses 
  cntLearnedIcs ::  [ImplClause Name],     -- learned implication clauses 
  cntAccIcs ::  [ImplClause Name],     -- accumulator for implication clauses
  cntNameFormList ::  [(Name, Form Name)],  -- list (Name,Form) corresonding to the Cache
  cntSubst :: Substitution,  -- substituttion name |-> form
  accModel :: Model Name,          -- current model
  wrongModels :: [(String,Model Name)] -- list of (name,wrongModel) where:
                                       -- wrongModel:  model not satisfying the semantic constraints
                                       --              (thus, wrongModel triggers a semantic restart)
                                       --       name:  name of wrongModel     
  }



data Size = Small | Large
  deriving Eq

data SeqI  =  SeqI(Int, Name)         -- SeqI(k,g)   represents the sequent   R_k, X  =>  g 
data SeqC  =  SeqC(Int,[Name],Name)   -- SeqC(k,A,b) represents the sequent   R_k, A |--c b    (classical provability) 

data Derivation  =
   LeafAxiom SeqC
  | RuleEnd (SeqI, Derivation )  -- top rule of a derivation  
  | RuleImpl( SeqI, SeqC, Derivation, Int) --  RuleImpl(root,axiom, der', k )
                                           --  k is the index of the main implication formula




mkContext ::  ProverEnv -> ProverState -> Context
mkContext env pst =
  let nameFormList = cache_to_sortedNameFormList (nameCache pst) ++ [(mainGoalName,inputFormula env)]
      initIcs = initImplClausesName env pst
  in
    Context{
     cntGoal = initGoalName env pst,
     cntInitCs =  initClausesName env pst,
     cntAddedCsBasic = reverse $ addedCsBasicName pst,
     cntAddedCsSem   = reverse $ addedCsSemName pst,
     cntInitIcs =  initIcs,
     cntLearnedIcs =   reverse $  addedIcsSemName  pst,
     cntAccIcs =  initIcs,
     cntNameFormList =  nameFormList,
     cntSubst = Map.fromList  nameFormList,
     accModel = emptyModel,
     wrongModels = []
     }




getIndexIc :: ImplClause Name  -> State Context Int
getIndexIc  ic =
  do
    context <- get
    let allIcs = cntInitIcs context ++ cntLearnedIcs context
    -- return $ fromJust $ (elemIndex  ic)  allIcs  
    return $ fromMaybe (-1) $ (elemIndex  ic)  allIcs



-- ##################################################

writeLatexTrace ::  ProverEnv -> ProverState  -> (String,[(String,Model Name)])
-- return (strTrace,wrongModels) where:
--   strTrace:   string representing the trace
-- wrongModels:  list  (name,wrongModel) of models not satisfying the semantic constraints

writeLatexTrace env pst  =
    let context = mkContext env pst
        (strTraceSteps,wrongModels) = evalState ( writeTraceAndProblemDescription env pst ) context
        strTraceProblem = preamble Large
                          ++ writeProblemPresentation env pst
                          ++ strTraceSteps
                          ++ endDocument
    in   (strTraceProblem, wrongModels)                  
        
 
{-  
writeLatexTrace env pst  =
    let context = mkContext env pst
    in    
    preamble Large
    ++ writeProblemPresentation env pst
    ++ evalState ( writeTraceAndProblemDescription env pst ) context
    ++ endDocument
-}


writeLatexDerivation ::  ProverEnv -> ProverState  -> String
writeLatexDerivation env pst  =
    preamble Small
    ++ "TO DO"
    -- ++ writeProblemName env
    -- ++  writeDerivation  (  writeDerivation env  pst )
    ++ endDocument



-- #################   TRACE  ###########################


writeProblemPresentation :: ProverEnv -> ProverState  -> String
writeProblemPresentation env pst  =
  let result =  if  isValidForm pst then "{\\bf Proved}"
                else "{\\bf Countsat}"
      ltToNm =  litToName pst
      countMod = if  isValidForm pst then ""
                 else writeNL 1 ++  "Worlds in the countermodel: " ++ show (sizeModel $ model pst )
  in
  writeProblemName env  
  -- ++ "\\[\n"
  -- ++ " \\provesl{R_0, X_0}{" ++ ( writeName . ltToNm . initGoal) env  ++ "}\\,? \n" 
  -- ++  "\\]\n"
  ++ "Input formula: " ++ (writeInMath .writeForm . inputFormula ) env 
  ++ writeNL 1
  ++ "Logic:  " ++  (show . logic) env  
  ++ writeNL 1 ++  result
  ++ writeNL 2
  -- ++ "Clauses in $R_0$: " ++  (show . length . initClauses) env
  -- ++ writeNL 1
  -- ++ "Clauses in $X_0$: " ++  (show . length  .initImplClauses) env
  -- ++ writeNL 1
  -- ++ "Atoms: " ++  (show . countAtms) env
  -- ++ writeNL 1
  -- ++ "New atoms: " ++  (show  . countNewAtms) pst
  -- ++ writeNL 1
  -- ++ "Calls to the SAT-solver: " ++ (show . countSat) pst
  -- ++ writeNL 1
  -- ++ "Restarts: " ++  (show . countRest) pst
  -- ++ writeNL 1
  -- ++ "Basic restarts: " ++  (show  .countRestBasic) pst
  -- ++ writeNL 1
  -- ++ "Semantic restarts: " ++  (show . countRestSem) pst
  -- ++ countMod
  -- ++ writeNL 1
  ++ "Clauses in $R_0$ (" ++    (show . length . initClauses) env     ++ ") are defined at the end of the document" 
  ++ writeNL 1
  
writeProblemName :: ProverEnv   -> String
writeProblemName env =
   "\\subsection*{Problem  \\lstinline|" ++ problemName env ++ "|}\n"

writeTraceAndProblemDescription ::  ProverEnv -> ProverState  -> State Context (String,[(String,Model Name)])
writeTraceAndProblemDescription env pst =
  do
    context <- get
    let initCs  = cntInitCs context
        initIcs = cntInitIcs context
    strIcs <- writeContextIcs   initIcs
    let strX0 =  "Implication clauses in $X_0$ ("
                 ++ show (length initIcs ) ++  "):"
                 ++ ( if null initIcs then ""  else writeNL 1 ++ strIcs )
    let subst = cntSubst context  
        nameFormList = cntNameFormList context   
        currentNames = getClausesNames initCs ++  getImplClausesNames  initIcs
        k = length [ p | (p,_) <-  nameFormList , p `elem` currentNames ]    
        strMap =  writeNameFormSubstList  (k-1) subst nameFormList -- do not print the map for g
        strSubst = writeNL 1 ++ "Substitution" ++  writeNL 1 ++  strMap   -- ??????  
    strTrace  <- writeTrace env pst
    strDescr  <- writeProblemDescription  env pst
    finalContext <- get
    return   ( strX0  ++ strSubst ++ strTrace ++ strDescr , wrongModels finalContext )
      
writeProblemDescription ::  ProverEnv -> ProverState  -> State Context String
writeProblemDescription env pst   =
  do
    context <- get
    let initCs =  cntInitCs context
        initIcs = cntInitIcs context
        ltToNm_map =   litToName_map  pst
        addedCsBasic = cntAddedCsBasic context
        addedCsSem =   cntAddedCsSem context
        addedAxs = map  (fmap ( ltToNm_map Map.!))    (addedAxioms pst)
        subst = cntSubst context
        addedAxsSubst = map  (applySubst subst) addedAxs
        addedIcsSem =  cntLearnedIcs context
        nameFormList = cntNameFormList context
        strMap =  writeNameFormSubstList  (length nameFormList - 1 ) subst nameFormList -- do not print the map for g
    strCs <-  writeContextCs  initCs
    strIcs <- writeContextIcs  initIcs
    strAddedCs <- writeContextCs  addedCsBasic
    strAddedCsSem  <-   writeContextCs  addedCsSem
    strAddedIcsSem  <-   writeContextIcs addedIcsSem
    return $
      "\n\\subsection*{Problem description}\n"
      ++ "Restarts: " ++  (show . countRest) pst
      ++ " (" ++ (show  .countRestBasic) pst ++ " basic, "
      ++  (show . countRestSem) pst ++ " semantic)"
      ++ writeNL 1
      --------
      ++ "Learned axioms ("
      ++ (show . length) addedAxs  ++  "):"
      ++ ( if null addedAxs then ""
           else    writeNL 1 ++   (writeInMath . writeFormsNL ) addedAxsSubst  )
      ++ writeNL 1 
      ---------------------------
      ++ "Flat clauses $R_0$ ("
      ++ (show . length) initCs ++  "):"
      ++ ( if null initCs then "" else  writeNL 1 ++  strCs )
      ++ writeNL 1 
      -----------------------------
      ++ "Implication clauses $X_0$ ("
      ++ (show . length) initIcs ++  "):"
      ++ ( if null initIcs then ""  else writeNL 1 ++ strIcs )
      ++ writeNL 1
      ---------------------------
      -- ++ "Learned axioms ("
      -- ++ show (length addedAxs ) ++  "):"
      -- ++ ( if null addedAxs then ""
      --     else    writeNL 1 ++   writeInMath ( writeFormsNL addedAxs ) )
      -- ++ writeNL 1 
      ---------------------------
      ++ "Clauses added in basic restarts ("
      ++ (show . length) addedCsBasic ++  "):"
      ++ ( if null addedCsBasic then "" else writeNL 1 ++ strAddedCs )
      ++ writeNL 1 
      ---------------------------
      ++ "Clauses added in semantic restarts ("
      ++ (show . length) addedCsSem ++  "):"
      ++ ( if null addedCsSem then "" else writeNL 1 ++ strAddedCsSem )
      ++ writeNL 1 
     ---------------------------
      ++ "Implication clauses learned in semantic restarts ("
      ++ (show . length) addedIcsSem ++  "):"
      ++ ( if null addedIcsSem then "" else  writeNL 1 ++ strAddedIcsSem )
      ++ writeNL 1 
     ---------------------------
      ++ "Substitution" ++  writeNL 1 ++  strMap
      
writeContextIcs ::  [ImplClause Name] ->  State Context   String
writeContextIcs   [] =  return ""
writeContextIcs   (ic : ics) =
 do
    strIc  <-  writeInMath <$> writeImplClauseDefinition  ic
    if null ics then return strIc
      else
      do
        strIcs <- writeContextIcs   ics
        return $  strIc ++ writeNL 1 ++ strIcs

writeImplClauseDefinition :: ImplClause Name -> State Context String
writeImplClauseDefinition  ic =
  do
    strIcName <- writeImplClauseSymbName  ic
    return $ strIcName ++ "\\,=\\," ++  writeImplClause ic


writeImplClauseSymbName :: ImplClause Name -> State Context String
writeImplClauseSymbName  ic   = writeLambda <$> getIndexIc ic 




writeContextCs :: [Clause Name] -> State Context String
writeContextCs   [] = return  ""    
writeContextCs  (c : cs) =
 do
  let strC =  ( writeInMath . writeClause )  c
  if null cs then return strC
    else
    do
      strCs <-  writeContextCs  cs
      return $  strC    ++ writeNL 1 ++ strCs




-- ##############################################   


writeTrace :: ProverEnv -> ProverState  -> State Context  String
writeTrace env pst =
 do
  strSteps <- writeSteps $ getSteps (traceName  pst)
  return $ beginTrace  ++ strSteps 




writeSteps  :: [TraceStep Name] -> State Context String
-- Non empty list of steps


-- writeSteps context    [] =  return ([] , emptyModel) -- never happens
writeSteps  [step] =
  do
  strStep <- writeStep step
  let result =
        case step of
           ProvedSat(_,_,_) -> "\\subsection*{Goal proved}"
           otherwise  ->   "\\subsection*{Countermodel found}"
  return $   strStep ++   endRestart ++ result


writeSteps (step1 : steps) =
  (++) <$>  (writeStep  step1) <*>  (writeSteps  steps) -- concatenate strings inside the monads

writeStep  :: TraceStep Name ->  State Context String
writeStep   step =
   do
    context <- get  -- get state
    strStep <-  writeStepStr  step
    case step of 
       NewWorld(wk,atms) ->
         do          
           let   newMod = addWorld (mkWorld wk atms) (accModel context)
           modify( \cnt -> cnt{accModel = newMod} )       
           strMod <- writeModel   newMod
           return $ strStep ++  "\n" ++ strMod
       NewSemClauses(_,_,_,_,_,_,_) ->
         do
           modify( \cnt -> cnt{accModel = emptyModel} ) 
           return strStep
       ProvedSat(_,_,_)  ->
         do
           modify( \cnt -> cnt{accModel = emptyModel} ) 
           return strStep
       _ -> return strStep


writeStepStr :: TraceStep Name ->  State Context String
writeStepStr (Check (k,ic))    =
 do
    strIc <- writeImplClauseDefinition  ic
    let strPair = "\\stru{\\,"  ++ writeW k ++ "\\,,\\," ++ strIc ++ "\\,}"
    return $
      "Selected:\n" ++  writeInMath strPair


writeStepStr   (AskSatR(cntSat,cntRet,right)) =
 return $  
  "\\item " 
  ++ writeInMath ( writeSqAsk (writeR cntRet) [] right )
   ++  "\n\n"

writeStepStr  (AskSatRW(cntSat,cntRet,wk,a,right)) =
 return $ 
  "\\item "
  ++ writeInMath ( writeSqAsk (writeR cntRet ++ ",\\," ++  writeW wk  ) [a] right )
  ++ "\n\n"
  
writeStepStr  (NewWorld(wInd,atms))  = 
 return $
  "$\\No{\\," ++ (writeNameSet . sort) atms ++ "\\,}$"
  ++ "\n\nNew world: "
  ++ (writeInMath . writeW) wInd    ++ "\n\n" 

writeStepStr  (ProvedSat (cntRet,xs,right)) =
 return $ 
  "$\\Yes{\\,"  ++ (writeNameSet . sort ) xs  ++ "\\,}$\n\n"
  ++ writeInMath (writeSqProved (writeR cntRet) xs right )
  ++ "\n\n" 
  
writeStepStr  (NewBasicClause(cntSat, cntRest, c) ) =
 do
   strAdded  <-   writeContextCs   [c]
   return $
     "Learned basic clause: "  ++  strAdded
     ++ writeNL 1
     ++ writeInMath (writeR (cntRest + 1) ++ "\\,=\\," ++ writeR cntRest ++ " + " ++ writeMBox "learned basic clause" )
     ++ endRestart
     ++ beginRestart (cntSat + 1) (cntRest + 1) Basic

  
writeStepStr  (NewSemClauses(cntSat, cntRest, chSize,newCs, newIcs, newAxioms,wrongModel) ) =
  do
   context <- get
   let wrongMods = wrongModels context
       wModName = "mod" ++ (show .length) wrongMods
       nameFormList = cntNameFormList context
       subst = cntSubst context
       newAxiomsSubst = map (applySubst subst) newAxioms
   modify ( \cnt ->  cnt{ cntAccIcs = newIcs ++ cntAccIcs cnt , wrongModels = (wModName,wrongModel) : wrongMods} )
   strAddedCs  <-  writeContextCs  (reverse newCs)
   strAddedIcs <-  writeContextIcs  newIcs
   return $
     "Check the obtained model " ++ wModName ++ " (see file " ++ writeInVerbatim wModName ++ ".png)"
     ++ writeNL 1
     ++ writeBold "Semantic failure"
     ++ writeNL 1
     ++ "Learned axiom:"  --  (" ++ (show. length) newAxioms  ++ "):" 
     ++  writeNL 1
     ++  ( writeInMath . writeForms ) newAxioms 
     ++  writeNL 1
     --------------------------------------
     ++ "New clauses after clausification (" ++ (show . length) newCs ++ "):" 
     ++  ( if (null  newCs) then "" else ( writeNL 1 ++ strAddedCs ) )
     ++  writeNL 1
     --------------------------------------
     ++ "New implication clauses after clausifications (" ++ ( show . length) newIcs ++ "):" 
     ++  ( if (null  newIcs) then "" else ( writeNL 1 ++ strAddedIcs ) ) 
     ++  writeNL 1
     ++ writeInMath (writeR (cntRest + 1) ++ "\\,=\\," ++ writeR cntRest  ++  writeMBox " + new  clauses " )
     ++  writeNL 1
     -----------------------------------
     -- ++ "Map" ++  writeNL 1 ++  writeNameFormList chSize nameFormList
     -- ++  writeNL 1
     -----------------------------------
     ++ "Substitution" ++  writeNL 1 ++  writeNameFormSubstList chSize subst nameFormList
     ++ writeNL 1
     -----------------------------------
     ++ "Learned axiom with  the substitution applied" -- (" ++ (show. length) newAxioms  ++ "):" 
     ++  writeNL 1
     ++  ( writeInMath . writeForms ) newAxiomsSubst 
     ++ endRestart
     ++ beginRestart (cntSat + 1) (cntRest + 1) Semantic


beginTrace ::  String
beginTrace =  
   "\n\\subsubsection*{Start }\n\n"
   ++ "\\begin{enumerate}[label=(\\arabic*),start=1]\n"


beginRestart :: Int -> Int -> ImplClauseType -> String
-- Basic or Semantic restart
beginRestart cntSat  cntRest cType  = -- | cntSat > 0, cntRest > 0 =
   "\n\\subsubsection*{Restart " ++ show cntRest ++  " (" ++ show cType ++ ")}\n\n"
   ++ "\\begin{enumerate}[label=(\\arabic*), start=" ++ show cntSat ++ "]\n" 


endRestart :: String
endRestart = "\n\\end{enumerate}\n"

writeSqAsk :: String -> [Name] -> Name -> String
writeSqAsk str [] right =
  "\\provesc{" ++ str ++ "}{"  ++ writeName right ++ "}\\;?"

writeSqAsk str xs  right =
 "\\provesc{" ++ str ++ ",\\," ++ writeSortedNames ",\\, " xs ++  "}{"
    ++ writeName right ++ "}\\;?"

writeSqProved :: String -> [Name] -> Name -> String
writeSqProved  str [] right =
  "\\provesc{" ++str ++ "}{" ++ writeName right ++ "}"
writeSqProved str xs  right =
  "\\provesc{" ++str ++ ",\\," ++ writeSortedNames ",\\, "  xs  ++ "}{" 
  ++ writeName right ++ "}"



-- #################   MODEL  ###########################


writeModel :: Model Name -> State Context  String
writeModel mod | isEmptyModel mod  = return "\\emptyset"  
writeModel mod =
  do
    strWorlds  <- ( writeWorlds . worlds) mod
    return $
      "\\begin{center}\n"
      ++ "\\small\n"
      ++ "\\begin{tabular}{l|l|l}\n"
      ++ headerModel
      ++ writeNL 1
      ++ "\\hline" ++ writeHLine
      ++  strWorlds  
      ++  "\n\\end{tabular}\n"
      ++ "\\end{center}\n\n"
  
writeHLine :: String
writeHLine = "\\hline &&\\\\[-1.5ex]\n"

  
headerModel :: String
headerModel = 
  "$W$ & & $\\lambda$ s.t.~$w\\nrealof{W}\\lambda$" 

writeWorlds :: [World Name] ->  State Context  String
-- ASSUMPION: nonempty world list
writeWorlds  [w]   =
  writeWorldDescription  w 

writeWorlds  (w1:ws)   =
  do
    strW1 <- writeWorldDescription w1
    strWs <- writeWorlds ws 
    return $
      strW1 ++ writeNL 1 ++ writeHLine ++ strWs

writeWorldDescription ::  World Name ->  State Context  String
writeWorldDescription w =
  do
  context <- get 
  let wk = worldIndex w
      atms = worldAtms w
      allIcs = cntInitIcs context ++ cntLearnedIcs context -- ?
      mod = accModel context
      icsToCheck_w  = icsToCheck (cntAccIcs context)  mod w
      -- icsBasicToCheck  = icsToCheck allIcs  mod w
  -- icsBasicSymb <- mapM  writeImplClauseSymbName       icsToCheck_w -- ics basic to be checked
  icsToCheck_w_indexes <- mapM getIndexIc icsToCheck_w -- indexes of ics basic to be checked
  let strIcs =
        if ( null icsToCheck_w_indexes ) then "$\\emptyset$"
        else
          writeInMath  ( writeList writeLambda (sort icsToCheck_w_indexes) )
  return $  
     (writeInMath . writeW) wk
     ++ " & "
     ++ (writeInMath . writeSortedNamesEmptyset ) atms 
     ++ " & "
     ++ strIcs  ++ "\n"



icsToCheck :: [ImplClause Name]  -> Model Name -> World Name -> [ImplClause Name]
icsToCheck ics mod w =
  [ ic | ic <- ics , not ( realizes (mod,w) ic ) ]


writeW :: Int -> String
writeW k = "w_{" ++ show k ++ "}"


writeWorld :: Int -> [Name] -> String
writeWorld k xs =  writeW k ++  "\\,=\\," ++ writeNameSet xs


-- #################   DERIVATION  ###########################

writeDerivation :: Derivation -> String
writeDerivation  der =  "TO DO"



---- ######   NAME CACHE  #####

writeNameFormList ::  Int -> [(Name, Form Name)]   -> String
-- write k elements of the map  name |-> form 
writeNameFormList 0 _ =  writeInMath $ writeName mainGoalName ++ "\\; \\mapsto\\;\\mbox{input formula}"  

writeNameFormList k ( (name,form) : nfs ) =
  let str =  writeInMath  ( writeName name ++ "\\; \\mapsto\\;" ++ writeForm form )
  in
  str ++ writeNL 1 ++ writeNameFormList (k - 1 )nfs

  
writeNameFormSubstList ::  Int -> Substitution -> [(Name, Form Name)]   -> String
-- write k elements of the map  name |-> form wit substitutions
writeNameFormSubstList 0 _ _ = ""
writeNameFormSubstList  k subst nameFormList   =
  let  nameFormSubstList =  map (\(name,form) ->  (name, (applySubst subst form)) ) nameFormList
  in  writeNameFormList k  nameFormSubstList

  


-- ###############  PRIMITIVE FUNCTIONS  ###############

beginArray :: String -> String
beginArray format =  "\n\\[\n\\begin{array}{" ++ format ++ "}\n"

endArray :: String
endArray =  "\n\\end{array}\n\\]\n"

writeMBox :: String -> String
writeMBox str = "\\mbox{" ++ str ++ "}"

writeNL :: Int -> String
writeNL k = "\n\\\\[" ++ show k ++ "ex]\n"

writeBold :: String -> String
writeBold str = "{\\bf " ++ str ++ "}"


writeR :: Int -> String
writeR k = "R_{" ++ show k ++ "}"

writePhi :: Int -> String
writePhi k = "\\varphi_{" ++ show k ++ "}"


writePsi :: Int -> String
writePsi k = "\\psi_{" ++ show k ++ "}"

writeLambda :: Int -> String
writeLambda k = "\\lambda_{" ++ show k ++ "}"

writeNameSet :: [Name] -> String
writeNameSet [] = "\\emptyset"
writeNameSet xs = "\\{\\," ++ writeSortedNames  ",\\, " xs ++ "\\,\\}"

writeInMath :: String -> String
writeInMath s = "$" ++ s ++ "$"

writeInVerbatim :: String -> String
-- writeInVerbatim  s = "\\verb|" ++ s ++ "|"
writeInVerbatim  s = "{\\tt " ++ s ++ "}"

writeList :: Show a => (a -> String ) -> [a] -> String
writeList f []  = "" 
writeList f [x] = f x
writeList f (x1 : xs)  =
  f x1 ++ ",\\, " ++ writeList f xs 



writeClause :: Clause Name -> String
writeClause  ( xs  :=> ys ) =
     case (xs,ys) of
      ([],[]) -> "\\bot" 
      ([],ys) ->  writeSortedNames "\\lor" ys
      (xs,[]) ->  writeSortedNames "\\land" xs ++ "\\to \\bot"
      (xs,ys) ->  writeSortedNames "\\land" xs ++ "\\to " ++  writeSortedNames "\\lor" ys




writeClauses :: [Clause Name] -> String
writeClauses cs  = writeList writeClause  cs



writeImplClause :: ImplClause Name -> String
writeImplClause ((a :-> b) :-> c) =
  "(" ++ writeName a ++ "\\to " ++ writeName b ++ ")\\to " ++ writeName c


-- main function to write a name
writeName :: Name -> String
writeName s | s == false = "\\bot"
writeName s | s == mainGoalName = "\\goal"
writeName ('$' : atm) =
  let (atmName, k ) = splitName atm
  in "\\newAtm{" ++ atmName ++ "}{" ++ k ++ "}"
writeName atm =
  let (atmName, k ) = splitName atm
      safeName = writeSafeName atmName  
  in
  if null k then safeName else safeName ++ "_{" ++ k ++ "}"

writeSortedNames :: String ->  [Name] -> String
writeSortedNames sep xs =  writeNames sep (sortNames xs) 

writeNames :: String ->  [Name] -> String
-- sep: separator between names
writeNames sep [] = ""
writeNames sep [x] = writeName x
writeNames sep (x:xs) = writeName x ++ sep ++  writeNames sep xs



writeSortedNamesEmptyset :: [Name] -> String
writeSortedNamesEmptyset [] = "\\emptyset"
writeSortedNamesEmptyset  xs = writeSortedNames ",\\, " xs


writeListEmptyset :: [Name] -> String
writeListEmptyset  [] = "\\emptyset"
writeListEmptyset  [x] = x
writeListEmptyset  (x:xs) = x ++ ",\\, " ++  writeListEmptyset xs

writeSafeName  :: String -> String
-- handle special symbols ($, _, ....)
writeSafeName name  = "{" ++ concatMap writeSafeChar name  ++ "}"

writeSafeChar :: Char -> String
writeSafeChar c | c == '$' || c== '%' || c == '_' = "\\" ++ [c]
writeSafeChar '\\' = "\\backslash "
writeSafeChar '#' = "\\sharp "
writeSafeChar c = [c]


-- ########################


preamble :: Size -> String
preamble size =
  preamble1 ++ preambleWidth size ++ preamble2

  
preamble1 = [r|\documentclass[10pt]{article}
\usepackage{proof}
\usepackage{enumitem}
\usepackage{listings}
\usepackage{amssymb}
|]  -- end string


preambleWidth Small =  [r|
\pdfpagewidth 80in  
%%\pdfpagewidth 200in %% MAX WIDTH
|]  -- end string

preambleWidth  Large =  [r|
%%\pdfpagewidth 80in  
%%\pdfpagewidth 200in %% MAX WIDTH
|]  -- end string

  

preamble2 :: String
preamble2 =  [r|
\newcommand{\goal}{\tilde{g}}
\newcommand{\newAtm}[2]{\tilde{#1}_{#2}}     
\newcommand{\seq}[2]{#1\, \Rightarrow\, #2}
\newcommand{\provesl}[2]{{#1}\,\vdash_{L}\, #2}
\newcommand{\provesc}[2]{{#1}\,\vdash_{\mathrm{c}}\, #2}
\newcommand{\stru}[1]{\langle #1 \rangle} % structure
\newcommand{\Yes}[1]{\mathrm{Yes}(#1)}
\newcommand{\No}[1]{\mathrm{No}(#1)}
\newcommand{\nrealof}[1]{{\ntriangleright}_{#1}}

\begin{document}

\thispagestyle{empty}

|]  -- end string



endDocument = "\n\\end{document}"


-- ###### WRITE FORMULA  #######
-- latex pretty print of formulas (avoiding redundant parenthesis)

betweenParens :: String -> String
betweenParens f = "(" ++ f ++ ")"  


writeForm :: Form Name -> String  

writeForm TRUE = "\\top"
writeForm FALSE = "\\bot"

writeForm (Atom a) = writeName a

writeForm (f1 :&: f2) =
 let wf1 = writeForm f1
     wf2 = writeForm f2
     wf1' = if (mainLogicalOp f1) `elem`[ NoOp,AndOp,NegOp] then wf1 else betweenParens wf1
     wf2' = if (mainLogicalOp f2) `elem`[ NoOp,AndOp,NegOp] then wf2 else betweenParens wf2
 in wf1'  ++ "\\land " ++  wf2'

writeForm (f1 :|: f2) =
 let wf1 = writeForm f1
     wf2 = writeForm f2
     wf1' = if (mainLogicalOp f1) `elem`[ NoOp,OrOp,NegOp] then wf1 else betweenParens wf1
     wf2' = if (mainLogicalOp f2) `elem`[ NoOp,OrOp,NegOp] then wf2 else betweenParens wf2
 in wf1'  ++ "\\lor " ++  wf2'

writeForm (f1 :=>: FALSE) =
  writeNegForm f1


writeForm (f1 :=>: Atom f2 ) | f2 == false  =
  writeNegForm f1

writeForm (f1 :=>: f2 )  =
 let wf1 = writeForm f1
     wf2 = writeForm f2
     wf1' = if (mainLogicalOp f1) `elem`[ NoOp,NegOp] then wf1 else betweenParens wf1
     wf2' = if (mainLogicalOp f2) `elem`[ NoOp,NegOp] then wf2 else betweenParens wf2
 in wf1'  ++ "\\to " ++  wf2'

writeForm (f1 :<=>: f2 )  =
 let wf1 = writeForm f1
     wf2 = writeForm f2
     wf1' = if (mainLogicalOp f1) `elem`[ NoOp,NegOp] then wf1 else betweenParens wf1
     wf2' = if (mainLogicalOp f2) `elem`[ NoOp,NegOp] then wf2 else betweenParens wf2
 in wf1'  ++ "\\leftrightarrow    " ++  wf2'

writeNegForm :: Form Name -> String  
writeNegForm f1 =
  let wf1 = writeForm f1
      wf1' = if (mainLogicalOp f1) `elem`[ NoOp,NegOp] then wf1 else betweenParens wf1
  in "\\neg " ++  wf1'





writeForms :: [Form Name] -> String  

writeForms [] = ""
writeForms [f] = writeForm f
writeForms (f:fs)  = writeForm f ++ "\\qquad" ++ writeForms fs 



writeFormsNL :: [Form Name] -> String  

writeFormsNl [] = ""
writeFormsNL [f] = writeForm f
writeFormsNL (f:fs)  = writeForm f ++ writeNL 1 ++ writeFormsNL fs 





-- ######## 

-- print the encoding of new atoms 
{-

writeFormIndexes :: FormIndexes -> String

writeFormIndexes formIndexes =
  let indexFormList = sort $ (map swap) $ Map.toList $ formIndexMap formIndexes
  in
  if null  indexFormList then ""
  else
    beginArray "lcl"
    ++ writeFormIndexList indexFormList
    ++ endArray 
  where
    swap (x,y) = (y,x)


writeFormIndexList :: [(Int,Form)] -> String


writeFormIndexList [] = ""
writeFormIndexList ((k,form) : xs)  =
  let pk = Atom ( "$p" ++ show k ) in
  writeForm  pk ++ " & \\,= \\,& "  ++ writeForm form 
  ++ if null xs then ""
     else writeNL 1  ++ writeFormIndexList xs 

-}

{-

writeFormIndex :: (Int,Form) -> String
writeFormIndex k form =
  let pk = Atom ( "$" ++ show k ) in
  writeForm  pk ++ " & \\,= \\,& " 

-}
