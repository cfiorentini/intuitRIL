{-# LANGUAGE TypeOperators #-}

module Jankov (
  checkModel    --   Ord a => Model a ->  [a] ->  [Form a]
)
  where



import Language 
import Model

{-

SEMANTIC

One maximal element

CHARACTERISTIC AXIOM

 ~A  v ~~A


-}

checkModel :: Ord a =>   Model a ->  [a] ->   [Form a]
{-

Assume that the model has two distinct maximal worlds w0 and w1.
We select an atom a in inputAtms such that:

 w0 |-- a   and    w1 |-/- a

OR

 w0 |-/- a   and   w1 |-- a

We build the axiom

 ~a v ~~a

-}

checkModel mod inputAtms  =
  let ws = maxWorlds mod
  in
  if length ws  == 1 then []
  else -- length ws > 1 
    let
      w0 = ws !! 0
      w1 = ws !! 1
      case1 =  [ Atom a | a <- inputAtms, a `elem` worldAtms w0, not (a `elem` worldAtms w1) ]
      case2 =  [ Atom a | a <- inputAtms, a `elem` worldAtms w1, not (a `elem` worldAtms w0) ]           
      p = head $ case1 ++ case2           
    in [ negf p :|:  negf (negf p)  ] 

