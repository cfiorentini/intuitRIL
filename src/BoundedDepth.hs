{-# LANGUAGE TypeOperators #-}

module BoundedDepth (
  checkModel    --  Ord a =>  Model a -> Int ->  [Form a]
)
  where


import Language 
import Model

{-

BD(n)

SEMANTIC

depth at most n 


dept(K) = n IFF there is a chain of n world AND
                no chain with more than n worlds




CHARACTERISTIC AXIOMS bd(n)

bd(1)   = p1 v ~p1

bd(2) = p2 v ( p2 ->  (p1 v ~p1) )

bd(3) = p3 v ( p3 -> ( p2 v ( p2 ->  (p1 v ~p1) )) )
...


-}



checkModel :: Ord a =>   Model a ->  Int ->   [Form a]
checkModel mod n =
  let   maxChain = getMaximalLengthChainFromWorld (root mod) mod
  in
  if length maxChain <= n then []
  else
    buildAxiom $ take (n + 1) maxChain 

buildAxiom :: Ord a =>   [ World a ]  ->  [Form a]
buildAxiom maxChain   =
  -- maxChain = [w1 .. w(n+1)]
  let ws = tail maxChain  --  [w2 .. w(n+1)]
      atms = zipWith worldAtmDifference ws maxChain
   -- atms = [p1 ... pn] where
   -- w1 |-/- p1,   w2 |-/- p2  ...       wn  |-/- pn
   -- w2 |--  p1,   w3 |--  p2   ...   w(n+1) |--  pn   
  in [bd atms] 

bd :: [Form a]  -> Form a
-- bd: non empty list of atoms
bd [p1] = p1 :|: negf p1
bd (p1 :ps) =
  p1 :|: ( p1   :=>: bd ps )



-- TEST
{-

         w7
          |
    w5   w6
  /   \  / 
 |     w4
 |     / \    
w1   w2   w3 
  \  |   /
     w0

-}

atms0 = []
atms1 = ["p1"]
atms2 = ["p2"]
atms3 = ["p3"]
atms4 = ["p4"] ++ atms2 ++ atms3
atms5 = ["p5"] ++ atms1 ++ atms4
atms6 = ["p6"] ++ atms4
atms7 = ["p7"] ++ atms6


w0 = mkWorld 0 atms0
w1 = mkWorld 1 atms1
w2 = mkWorld 2 atms2
w3 = mkWorld 3 atms3
w4 = mkWorld 4 atms4
w5 = mkWorld 5 atms5
w6 = mkWorld 6 atms6
w7 = mkWorld 7 atms7


mod1 = mkModel [ w0, w1, w2, w3, w4, w5, w6, w7 ]
