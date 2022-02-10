{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module  WriteMakeFile
  (
    writeMakeFile   -- SearchResult -> TraceName -> DerOrModName   -> [WrongModelName] -> String
  )
where

import Text.RawString.QQ

import ProverTypes


type TraceName = String
type DerOrModName = String
type ModelName = String
type WrongModelName = String




writeMakeFile :: SearchResult -> TraceName -> DerOrModName -> [WrongModelName] -> String
writeMakeFile result   traceName derName wrongModelsNames =
   preamble result  traceName derName ++  body result  wrongModelsNames


preamble :: SearchResult -> TraceName ->   DerOrModName -> String
preamble result traceName derOrModName  =   
  "TRACE=" ++ traceName ++ "\n" ++
  if (result == Valid ) then  ""
   --  "DERIVATION=" ++  derOrModName   ++ "\n"
  else
    "COUNTERMODEL=" ++  derOrModName   ++ "\n"


  {-

NOTE: in Makefile, use TAB (and not spaces) 
To insert TAB: Ctrl q TAB

-}

body :: SearchResult ->   [WrongModelName]  -> String
body  result wrongModelsNames =
  body_all result
  ++ concatMap writeWrongModel wrongModelsNames
  ++ body_echoMsg result wrongModelsNames
  ++ body_clean


writeWrongModel :: WrongModelName -> String
writeWrongModel w =
  "\tdot " ++  w ++ ".gv -Tpng -o " ++ w ++ ".png\n"


{-

body_all :: SearchResult -> String
-- with derivations
body_all Valid = [r|
all:
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${TRACE}.tex  > /dev/null
	pdflatex -halt-on-error ${DERIVATION}.tex  > /dev/null
	@rm -f *.log  *.aux
|]  -- end string

-}
  
body_all :: SearchResult -> String
body_all Valid = [r|
all:
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${TRACE}.tex  > /dev/null
	@rm -f *.log  *.aux
|]  -- end string

body_all CountSat  = [r|
all:
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${TRACE}.tex  > /dev/null
	dot ${COUNTERMODEL}.gv -Tpng -o ${COUNTERMODEL}.png
	@rm -f *.log  *.aux
|]  -- end string


body_echoMsg :: SearchResult ->  [WrongModelName]  -> String
body_echoMsg  result wrongModelsNames =
  let strPdf   =  "\t@echo \"---> see the output in the obtained .pdf files\""
      strPdfPng = "\t@echo \"---> see the output in the obtained .pdf and .png files\""
  in
  if (result == Valid) &&  (null wrongModelsNames) then   strPdf  else  strPdfPng 
    

  
body_clean :: String
body_clean =[r|
clean:
	@echo  -- Cleaning  ...        
	@rm -f *.pdf  *.log  *.aux *.gv  *.png
|]  -- end string
