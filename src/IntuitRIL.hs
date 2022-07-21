{-# LANGUAGE TypeOperators, QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module Main where

-- import qualified Data.List as List
import Data.List
import Data.Char
import qualified Data.Map  as Map
import Text.RawString.QQ
import Data.Maybe
import Data.IORef
import System.IO
import Control.Monad ( when )
import Text.Printf
import System.Environment -- getArgs
import System.Console.GetOpt
import System.Exit
import System.CPUTime

--------
import Language
import ParserTPTP 
import Clausify
import Prover
import ProverTypes
import Utility
import WriteLatex 


-- #######  OPTIONS ######

data Flag
   =  TraceAndLatex        -- -t
  | TraceLevel Int         -- -tk where k=0 (low),1 (medium), 2 (high)
  | Debug                  -- -d
  | Clausify               -- -c
  | LogicName  Logic       -- -lx where x is the name of the logic 
  | Help                   -- -h
   deriving (Eq,Show)

flags =
       [
        Option ['c'] []       (NoArg Clausify)  "Apply the Clausification procedure to the input formula", 
        Option ['d'] []       (NoArg Debug)  "Debug",
        Option ['l'] []       (ReqArg argLogicName "Logic") "Logic",
        Option ['h'] []       (NoArg Help)    "Print this help message",
        Option ['t'] []       (OptArg argTraceLevel "Trace level")  "Trace and Latex"
       ]


argTraceLevel :: Maybe String -> Flag
argTraceLevel (Just k) = TraceLevel $ read  k
argTraceLevel Nothing = TraceAndLatex

argLogicName :: String -> Flag
argLogicName bdn | "bd"  `isPrefixOf` bdn =
                 -- example : "bd5" ---> Bd 5   
                 let n = read $ fromJust $ stripPrefix "bd" bdn
                 -- stripPrefix : delete the prefix "bd" from the string bdn
                 in LogicName ( Bd  n )
argLogicName  "gl"   = LogicName Dummett
argLogicName gln | "gl"  `isPrefixOf` gln =
                 -- example : "gl5" ---> GLn 5   
                 let n = read $ fromJust $ stripPrefix "gl" gln
                 -- stripPrefix : delete the prefix "gl" from the string gln
                 in LogicName ( GLn  n )                 
-- argLogicName  "ht"   = LogicName HereAndThere
argLogicName  "jn"   = LogicName Jankov
argLogicName  "kp"   = LogicName Kp
argLogicName  _      = LogicName Ipl -- default


--------------------------------------------------------------------------------
-- ###  MAIN ###

main :: IO ()
main =
  do
    (args, files) <- getArgs >>= parseArgs
    let logi =  getLogicArgs args  
        traceLev = getTraceLevelArgs args
        debug = Debug `elem` args
        file = head files
    putStrLn $ "+++ Logic: " ++ show logi
    putStrLn $ "+++ Reading file '" ++ show file ++ "'..."
    mForms <- parseFileTPTP file
    case mForms of
       Left err -> print err  >> fail "parse error"
       Right inputForms -> startProver logi traceLev  debug file (buildInputForm inputForms)
 
------------------------
-- parse arguments

parseArgs :: [String] -> IO ([Flag], [FilePath])
-- return arguments and input files in the command line 
parseArgs argv =
  case getOpt Permute flags argv of
        (args,inputFiles,[]) ->   -- empty list of error messages
          do
            if Help `elem` args then -- print help
              do
                hPutStrLn  stderr  help 
                exitWith ExitSuccess
            else if  null inputFiles  then -- no input file
              do
                hPutStrLn stderr $ "No input file" ++ help
                exitWith (ExitFailure 1) 
            else if Clausify `elem` args then  -- only clausify
              do  
                onlyClausifyInputFormulas (head inputFiles)
                exitWith ExitSuccess 
            else return  (args,inputFiles)  
        (_,_,errs)      ->  -- non-empty list of error messages
          do
            hPutStrLn stderr $ ( concat errs ) ++ help 
            exitWith (ExitFailure 1)
      


getLogicArgs ::  [Flag] -> Logic
-- default logic is Int
getLogicArgs args =
  let mlogi =  find isLogicName  args
  in 
  case mlogi of
    Just (LogicName l) ->  l
    _       -> Ipl


getTraceLevelArgs ::  [Flag] -> TraceLevel
getTraceLevelArgs args  =
  if ( TraceAndLatex `elem` args ) then TraceLevel_high_with_latex 
  else
    let mLevel = find isTraceLevel args
    in    
    case mLevel of
     Just (TraceLevel 0) -> TraceLevel_low
     Just (TraceLevel 1) -> TraceLevel_medium
     Just (TraceLevel 2) -> TraceLevel_high
     _   -> TraceLevel_low  -- DEFAULT

isTraceLevel :: Flag -> Bool
isTraceLevel (TraceLevel _) = True
isTraceLevel _              = False

isLogicName :: Flag -> Bool
isLogicName (LogicName _) = True
isLogicName _              = False



 -- -----------------------

-- IntuitR, a SAT-based prover for Intuitionistic Propositional Logic.

help :: String
help = [r|
Usage: intuitRIL [OPTION] FILE

FILE
  text file containing the input formula, see the README file for the syntax

TRACE OPTIONS
 -t     trace (maximum level) and generate output files 
 -t0    minimum trace level, no output files 
 -t1    medium  trace level, no output files
 -t2    maximum trace level, no output files (*default*)
 -d     debug (print additional information on the prover state)

LOGIC OPTIONS
-lipl   Intuitionistic Propositional Logic (*default*)
-lgl    Goedel-Dummett Logic               (linear frames)
-lglk   Goedel-Dummett Logic k             (linear frames, depth at most k)
-ljn    Jankov Logic                       (one maximal world)
-lkp    Kreisel and Putnam Logic          (condition on maximal worlds, see README)

OTHER OPTIONS
-c    only clausify the input formula
-h    print help 

|]-- end string

  

withParseFile ::  FilePath ->  Logic -> (Logic -> FilePath -> [Input (Form Name)] -> IO ()) -> IO ()
withParseFile file logi process =
  do putStrLn ("+++ Reading file '" ++ show file ++ "'...")
     mForms <- parseFileTPTP file
     case mForms of
       Left err -> print err  >> fail "parse error"
       Right inputForms -> do process logi file inputForms


  


startProver :: Logic -> TraceLevel -> Bool -> FilePath ->  Form Name  -> IO ()
startProver logi traceLev debug file  inputForm = 
  do 
     putStrLn  "+++ Clausification input formula ..."
     start1 <- getCPUTime
     let  (cache,atmIndex,cs,ics) = clausifyForms 0 [ inputForm :<=>: Atom mainGoalName]
      --  cs:   flat clauses
      --  ics:  implication clauses
      --  mainGoalName = "$goal"
      -- ASSUMPTION: mainGoalName does not occur in cs U ics    
          (countCs,countIcs) = (length cs, length ics)
     ( when( traceLev >=  TraceLevel_high) $
       do
           putStrLn ("+++ Created " ++ show countCs ++ " flat clauses and "
                              ++ show countIcs ++ " implication clauses")
           -- putStrLn $ "+++ Number of reduced implication clauses: " ++ show countIcsReductions
           putStrLn $ "==== FLAT CLAUSES (" ++ show countCs ++  ") ====" 
           putStr $ unlines $ map printClause cs 
           putStrLn $ "==== IMPLICATION CLAUSES (" ++ show countIcs ++  ") ====" 
           putStr $ unlines $ map printImplClause ics 
           ) -- end when
     putStrLn ("+++ Proving ... ")
     hFlush stdout
     end1 <- getCPUTime
     ( when( traceLev >=  TraceLevel_high) $
       do
         putStrLn $ "==== CACHE ====" 
         putStrLn $ printCache cache
       )
     start2 <- getCPUTime
     let cs' =  cs `union` closureImplClauses ics
     proveProblem  logi traceLev file cache  atmIndex inputForm cs' ics mainGoalName debug
     end2 <- getCPUTime
     let time_clausify =(fromIntegral (end1 - start1)) / (10^12)
         time_prover =  (fromIntegral (end2 - start2)) / (10^12)
     putStrLn $  concat $ replicate 80 "*"  
     printf "Clausification time: %0.3f sec\n" (time_clausify :: Double)
     printf "Prover time: %0.3f sec\n" (time_prover :: Double)


-- ############################à

onlyClausifyInputFormulas :: FilePath -> IO ()
onlyClausifyInputFormulas file =
  do
    putStrLn ("+++ Reading file '" ++ show file ++ "'...")
    mForms <- parseFileTPTP file
    case mForms of
       Left err -> print err  >> fail "parse error"
       Right inputForms ->
        do
          let form = buildInputForm inputForms    
              (cache, index, cs, ics) = clausifyForms 0 [form]
          putStrLn  $ "=== FORMULA ===\n" ++  printfForm id form 
          putStrLn  $ "=== CLAUSES (" ++ (show . length ) cs ++  ") ===\n" ++  printfClauses id cs 
          putStrLn  $ "=== IMPL. CLAUSES ("  ++ (show . length ) ics ++ ") ===\n" ++  printfImplClausesLn id ics 
          putStrLn  $ "=== INTERNAL MAP ===\n" ++  printCache cache
          putStrLn  $ "=== SUBSTITUTION ===\n" ++  printCacheSubst cache

