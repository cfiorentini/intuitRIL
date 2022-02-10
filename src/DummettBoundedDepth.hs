{-# LANGUAGE TypeOperators #-}

module DummettBoundedDepth (
  checkModel    --  Ord a =>  Model a -> [a] ->  [Form a]
)
  where


import Language 
import Model
import Data.Maybe
import qualified Dummett as Dummett

{-

SEMANTIC

1) Linear model
2) Depth at most n


1) CHARACTERISTIC AXIOM

 (A -> B) v  (B -> A)

2) CHARACTERISTIC AXIOMS bd(n)

bd(1)   = p1 v ~p1

bd(2) = p2 v ( p2 ->  (p1 v ~p1) )

bd(3) = p3 v ( p3 -> ( p2 v ( p2 ->  (p1 v ~p1) )) )
...

-}



checkModel :: Ord a =>   Model a ->  Int -> [a] ->  [Form a]
checkModel mod n inputAtms = 
  let dumAxs = Dummett.checkModel mod inputAtms 
  in
    if (not . null) dumAxs then dumAxs
    else bdCheckModel mod n inputAtms

 
bdCheckModel :: Ord a =>   Model a ->  Int ->  [a] ->  [Form a]
-- Assumption: mod is linear
bdCheckModel mod n inputAtms =
  let   maxChain = getMaximalLengthChainFromWorld (root mod) mod
  in
  if length maxChain <= n then []
  else
    buildAxiom   (take (n + 1) maxChain) inputAtms 

buildAxiom :: Ord a =>   [ World a ] -> [a] ->  [Form a]
buildAxiom maxChain inputAtms  =
  -- maxChain = [w1 .. w(n+1)]
  let ws = tail maxChain  --  [w2 .. w(n+1)]
      atms = zipWith (atmDifference inputAtms)  ws maxChain
   -- atms = [a1 ... an] such that:
   --  a1 .. an are in inputAtms   
   -- w1 |-/- a1,   w2 |-/- a2  ...       wn  |-/- an
   -- w2 |--  a1,   w3 |--  a2   ...   w(n+1) |--  an   
  in [bd atms] 

atmDifference ::  Ord a => [a] -> World a -> World a -> Form a
-- return atom a  such that  a in inputAtms and   w1 |-- a  and    w2 |-/- a
-- ASSUMPTION: there is at least such an a
atmDifference inputAtms w1 w2 =
  Atom $ head $
    [ a | a <- inputAtms,  a `elem` worldAtms w1, not ( a `elem` worldAtms w2) ]
  

bd :: [Form a]  -> Form a
-- bd [a1 ... an]
-- a1 v ( a1 => a2 v ( a2 => ... (an v ~an) ...))  
bd [a1] = a1 :|: negf a1
bd (a1 :as) =
  a1 :|: ( a1   :=>: bd as )



-- test
{-

atms = ["a", "b", "c"]

w0 = (mkWorld 0 []) ::  World Name
w1 = mkWorld 1 ["a", "p1"]
w2 = mkWorld 2 ["b", "p2"]



mod1 = mkModel [ w0, w1, w2 ]
test1 = checkModel mod1 atms

-- [(("a" => "b") | ("b" => "a"))]

w3 = mkWorld 3 ["a", "b"]

mod2 = mkModel [ w0, w1, w3 ]
{-

  a,p1    a,b
  w1       w3
    \     /
      w0
-}

test2 = checkModel mod2 atms
-- (("b" => ("b" => $false)) | (("b" => $false) => "b"))]

w4 = mkWorld 4 ["a", "b", "p1"]

mod3 = mkModel [ w0, w1, w3 , w4 ]

{-

      a,b,p1 
     w4 
   /       \
 w1 a,p1   w3 a,b   
   \      /
      w0

-}

test3 = checkModel mod3 atms
-- [((("a" => "b") => "a") | ("a" => ("a" => "b")))]

-}
