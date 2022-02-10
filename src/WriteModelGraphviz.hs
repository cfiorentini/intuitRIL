{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module  WriteModelGraphviz  
  (
     writeModelGraphviz  -- String -> Model Name -> String
                         -- args: problem name, args 
  )
where

import Text.RawString.QQ

import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.PartialOrd as POrd

import Language
import Model
import Utility

writeModelGraphviz :: String -> Model Name -> String
writeModelGraphviz problName mod  =
  preamble problName ++  graphSettings
  -- ++ "label=\"" ++ problName ++ "\"\n"
  ++ writeWorlds mod
  ++ writeSuccs mod
  ++ "} // end model\n"


  
buildSuccList :: Ord a => Model a -> [(World a, World a)]
-- [ (w,w') | w' is an immediate successor of w ]
buildSuccList mod =
  [ (w, w') |  w  <- worlds mod  , w' <-  immediateSuccList_w w mod ]



worldName :: World Name -> String
worldName w = "w" ++ (show . worldIndex) w 

writeWorldName w =  "w" ++ (writeSub . show . worldIndex) w 

writeSub :: String -> String
writeSub k = "<SUB>" ++  k ++ "</SUB>"


tildeCode :: String
tildeCode = "&#771;"

-- writeAtm :: Show a => a -> String
writeAtm :: Name -> String
writeAtm p | p == false = "&perp"
writeAtm p | p == mainGoalName = "g" ++ tildeCode

writeAtm ('$': atm) =
  let (atmName, k ) = splitName atm
  in
  case k of
    [] ->   atmName ++ ""
    _  ->   atmName ++ tildeCode ++ writeSub k 

writeAtm atm =
  let (atmName, k ) = splitName atm
  in
  case k of
    [] ->  atmName 
    _  ->  atmName  ++ writeSub k 


writeAtms :: [Name] -> String
writeAtms [] =""
writeAtms [p] = writeAtm p
writeAtms (p1:ps) = writeAtm  p1 ++ ", " ++ writeAtms ps



writeWorld ::  World Name -> String
writeWorld w =
  worldName w ++ "  [label = <"  
  ++ "<B>" ++  writeWorldName w ++ "</B>: "
 ++ (writeAtms . sortNames .worldAtms ) w ++ ">]"



writeWorlds :: Model Name -> String
writeWorlds mod =
  "\n// NODES\n" ++  unlines ( map writeWorld (worlds mod ) )
-- unlines :: [String] -> String
-- unlines ["a", "b", "c"] = "a\nb\nc\n"


writeSucc :: (World Name,World Name) -> String
writeSucc (w1,w2) = worldName w1 ++ " -- " ++ worldName w2


writeSuccs :: Model Name -> String
writeSuccs mod = 
  "\n// LINKS\n" ++  unlines ( map  writeSucc ( buildSuccList mod ) ) 
 

preamble :: String -> String
preamble src  =
  let srcgv = src ++ ".gv"
      srcpng = src ++ ".png" in
  "\
  \/***  SOURCE GRAPHVIZ FILE  ***\n\
  \\n\
  \Compile with:\n\
  \\n\
  \  dot " ++  srcgv ++   " -Tpng -o " ++ srcpng ++ "\n\
  \\n\
  \Edit this file or change the compilation options to modify the layout\n\
  \\n\
  \***/\n\n\
  \"

graphSettings :: String
graphSettings=[r|
graph ObjectDiagram {
  graph [
    rankdir= BT
    overlap = false
  ];
  node [
    fontsize = "16"
    shape = "record"
    style = filled
    fillcolor = palegreen
  ];
  fontsize=12;

|] -- end string


