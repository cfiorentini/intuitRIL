{-# LANGUAGE TypeOperators #-}

module Dummett (
  checkModel    --  Ord a =>  Model a -> [a] ->  [Form a]
)
  where


import Language 
import Model


{-

SEMANTIC

Linear model

CHARACTERISTIC AXIOM

 (A -> B) v  (B -> A)

-}



checkModel :: Ord a =>   Model a ->  [a] ->  [Form a]
checkModel mod inputAtms =
  let dumPairs = findDumPairs mod inputAtms
  in
    if null dumPairs then []
    else 
      let (f1,f2) = head dumPairs
      in [ (f1 :=>:  f2) :|:  ( f2 :=>:  f1 )]

findDumPairs  ::  Ord a =>  Model a -> [a] ->   [(Form a,Form a)]
{-  

Let us consider the call
 findDumPairs mod inputAtms

where:
- mod is a model
- inputAtms are the atoms in the input formula

Find a list of pairs of formulas (f1,f2) such that:

o  f1 and f2 only contain atoms from  inputAtms 
o  w1 |-- f1   and  w1 |-/- f2
o  w2 |-- f2   and  w2 |-/- f1

We consider 3 cases:

(1) f1 = a and f2 = b such that

o  (a \in inputAtms) and (b \in inputAtms)
o  there are w1 and w2 such that
   - (a \in  w1) and (a not\in w2)
   - (b \in  w2) and (b not\in w1)

    w1 |-- a   and  w1 |-/- b
    w2 |-- b   and  w2 |-/- 1

------------------------------------

(2) f1 = a and f2 = ~a such that

o  a \in inputAtms)
o  there are w1 and w2 such that
   - w1 and w2 are maximal worlds 
   - (a \in  w1) and (a not\in w2)

    w1 |-- a    and  w1 |-/- ~a
    w2 |-- ~a   and  w2 |-/- a

------------------------------------
(3) f1 = b => a and f2 = b such that  

o  (a \in inputAtms) and (b \in inputAtms)
o  there are w1, w2 and w3 such that:
   - w1 < w3 and w2 < w3
   - (a \in w3) and (a not \in w2)
   - (b \in w2) and (b not\in  w1)

          w3   a , b
        /   \
      w1     w2  b
  
     w1 |-- b => a   and  w1 |-/- b
     w2 |-- b        and  w2 |-/- b => a 

-}

findDumPairs mod inputAtms =
  let  ws = worlds mod
       max_ws =  maxWorlds mod 
       case1 = [ (Atom a, Atom b) |
                 a <- inputAtms,  b <- inputAtms,
                 w1 <- ws, w2 <- ws, not (w1 .<. w2), not (w2 .<. w1),
                 a `elem` worldAtms w1, not ( a `elem` worldAtms w2),
                 b `elem` worldAtms w2, not ( b `elem` worldAtms w1)
               ]
       case2 = [ (Atom a, negf (Atom a)) |
                 a <- inputAtms,  b <- inputAtms,
                 w1 <- max_ws, w2 <- max_ws, not (w1 .<. w2), not (w2 .<. w1),
                 a `elem` worldAtms w1, not ( a `elem` worldAtms w2)
               ]    
       case3 = [ (Atom b :=>: Atom a, Atom b) |
                  a <- inputAtms,  b <- inputAtms,
                  w1 <- ws, w2 <- ws, w3 <- ws,   
                  w1 .<.w3, w2 .<. w3,  not (w1 .<. w2), not (w2 .<. w1),
                  a `elem` worldAtms w3, not ( a `elem` worldAtms w2), 
                  b `elem` worldAtms w2, not ( b `elem` worldAtms w1)
               ]
  in case1 ++ case2 ++ case3


-- test

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
