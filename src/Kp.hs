{-# LANGUAGE TypeOperators #-}

module Kp (
  checkModel    --   Ord a => Model a -> [a] ->   [Form a]
)
  where

import qualified Data.Set as Set
import Data.Maybe
import Data.List

import Language
import Model

{-

SEMANTIC

For all w0, w1, w2 

   (w0 < w1)  &  (w0 <   w2)

  =>

  w0,  w1, w2  satisfy the following semantic condition:  

(SemCond)   there is w such that: 
               w0 <= w   &&   w <= w1   &&   w <= w2   &&
               maxWorlds(w) \subseteq  ( maxWorlds(w1) U  maxWorlds(w2) )

 maxWorlds(w) = maximal worlds w' such that w <= w'



      w1  w2
       \ /
        w  
         \   
          w0

CHARACTERISTIC AXIOM

 ( ~A  -> (B v C) ) -> ( (~A -> B) v (~A -> C) )  

-}


checkModel :: Ord a => Model a ->  [a] ->  [Form a]
checkModel mod inputAtms  =
  let ws = worlds mod
      triples = [ (w0,w1,w2) | w0 <- ws, w1 <- ws, w2 <- ws,
                               w0 .<. w1, w0 .<.w2, worldIndex w1 < worldIndex  w2 ] -- avoid duplicated checks
      mtriple =   find ( not . (satisfySemCond mod) ) triples   
  in
  case mtriple of
    Nothing -> []
    Just triple -> buildAxiomKP mod triple inputAtms 


-- satisfySemCond :: Model Lit -> (World Lit ,World Lit ,World Lit)  -> Bool
satisfySemCond :: Ord a => Model a -> (World a ,World a ,World a)  -> Bool
-- check if the triple  (w0, w1, w2) satisfies (SemCond)
satisfySemCond mod (w0,w1,w2)  =
  not . null $  [ w |  w <- worlds mod ,
                       w0 .<=. w , w .<=. w1 , w .<=. w2 ,
                       (maxWorlds_w w mod ) `isSubsetOf`  ( maxWorlds_w w1 mod ++ maxWorlds_w w2 mod ) ]
                      


buildAxiomKP ::  Ord a => Model a -> (World a ,World a ,World a)  -> [a] -> [Form a]
{-
buildAxiomKP mod (w0,w1,w2) inputAtms

where

 w1   w2
  \  /
   w0

Let maxWs12   = maxWorlds(w1) U  maxWorlds(w2) 
    maxWs12'  = maxWorlds(w0) \ maxWs12

There is H such that:
o H only contains atoms from inputAtms
o for every w in  maxWs12 ,  w |-- ~H
o for every w in  maxWs12',  w |-- H

There is a,b such that
o w1 |--  a  and  w2 |-/- a
o w1 |-/- b  and  w2 |--  b 

(we cannot guarantee that a and b are in inputAtms)

~H    ~H
 .    .
 .    .
 w1 a  w2 b    H
  \    |     /
   \   |    /

      w0  

The instance of axiom (KP) falsified in the model is

 (~H -> a v b) -> ( ~H -> a) v (~H -> b)

-}

buildAxiomKP mod (w0,w1,w2) inputAtms =
  let maxWs0 = maxWorlds_w w0 mod
      maxWs1 = maxWorlds_w w1 mod
      maxWs2 = maxWorlds_w w2 mod
      maxWs12 = nub $ (maxWs1 ++ maxWs2)
      maxWs12' = maxWs0 \\ maxWs12
      a = sepAtm_w_w w1 w2 inputAtms
      b = sepAtm_w_w w2 w1 inputAtms
      h = sepForm_ws_ws maxWs12' maxWs12 inputAtms
  in
  [ (negf h :=>: ( a :|: b) ) :=>: ( (negf h :=>: a ) :|:  (negf h :=>: b ) )]  


{-
test mod (w0,w1,w2) =
  let maxWs0 = maxWorlds_w w0 mod
      maxWs1 = maxWorlds_w w1 mod
      maxWs2 = maxWorlds_w w2 mod
      maxWs12 = nub $ (maxWs1 ++ maxWs2)
      maxWs12' = maxWs0 \\ maxWs12
  in
  ( maxWs0 ,  maxWs1, maxWs2 )
  -- ( maxWs12 ,  maxWs12')
--}



-- isSubsetOf ::   [World Lit] ->  [World Lit] ->  Bool
isSubsetOf ::  Ord a =>  [World a] ->  [World a] ->  Bool
isSubsetOf ws1 ws2 =
    (Set.fromList ws1) `Set.isSubsetOf`  (Set.fromList ws2) 


sepAtm_w_w :: Ord a => World a -> World a -> [a] -> Form a

{-

sepAtm_w_w w1 w2 inputAtms 

Find an atom p such that:

  w1 |--  p and w2 |-/- p

If possible, select w1 and w2 from inputAtms

ASSUMPTION:
w1 and w2 are distinct

-}

sepAtm_w_w w1 w2 inputAtms = 
  let atms1 = [ Atom a  | a <-  inputAtms ,  a `elem` worldAtms w1 ,  not ( a `elem` worldAtms w2 ) ]
      atms2 = [ Atom a  | a <-  worldAtms w1 ,  not ( a `elem` worldAtms w2 ) ]
  in head $ atms1 ++ atms2


sepForm_w_w :: Ord a => World a -> World a -> [a] -> Form a
{-

sepForm_w_w w1 w2 inputAtms 

Find a formula F such that

1) F only contains atoms from inputAtms 
2) w1 |--  F
3) w2 |-/- F

ASSUMPTION:
(*) there is p in inputAtms such that:
    (i)   p \in ( w1 \ w2)  OR
    (ii)  p \in  (w2 \ w1)

We set:

F =  p if (i) holds
    ~p otherwise 

-}

sepForm_w_w w1 w2 inputAtms = 
  let fs1 = [ Atom a         | a <-  inputAtms ,  a `elem` worldAtms w1 ,  not ( a `elem` worldAtms w2 ) ]
      fs2 = [ negf (Atom a)  | a <-  inputAtms ,  a `elem` worldAtms w2 ,  not ( a `elem` worldAtms w1 ) ]
  in head $ fs1 ++ fs2
  

sepForm_w_ws :: Ord a => World a -> [World a] -> [a] -> Form a
{-
sepForm_w_ws w [w1 .. wn]  inputAtms  

Build a formula F (separating formula) such that
1) F only contains atoms from inputAtms 
2) w  |--  F
3) wk |-/- F, for every k = 1 .. n  
ASSUMPTIONS:
a) n >= 1
b) for every wk, the pair of worlds (w,wk) satisfies (*)

We set

F = F1 & .... & Fn

where Fk = sepForm_w_w w wk inputAtms

-}

sepForm_w_ws w ws inputAtms =
  foldl1 (:&:)  $  nub (sepForm'_w_ws w ws inputAtms)
  where
    sepForm'_w_ws w (w1 : ws) inputAtms =  -- World a -> [World a] -> [a] -> [Form a]
      let f1 = sepForm_w_w w w1 inputAtms 
      in if null ws then [f1] else (f1 :  sepForm'_w_ws w ws inputAtms) 
  
  
sepForm_ws_ws :: Ord a => [ World a ] -> [World a] -> [a] -> Form a
{-
sepForm_ws_ws [w1 .. wm]  ws inputAtms

Build a formula F (separating formula) such that
1) wi |--  F,  for every i = 1 .. m
2) w' |-/- F,  for every w' in ws 

ASSUMPTIONS:
a) m >= 1 and ws is not empty
b) for every wi and w' in ws, the pair of worlds (wi,w') satisfies (*)


We set

 F = F1 | ... | Fm

where Fi = sepForm_w_ws wi ws

-}

sepForm_ws_ws (w1 : ws) ws' inputAtms =
 let f1 = sepForm_w_ws w1 ws' inputAtms 
 in if null ws then f1 else f1 :|:  sepForm_ws_ws ws ws' inputAtms 
  

         
{-

w0 = mkWorld 0 [] :: World Name
w1 = mkWorld 1 ["a"]
w2 = mkWorld 2 ["b"]

mod = mkModel [w0, w1, w2]
-}


