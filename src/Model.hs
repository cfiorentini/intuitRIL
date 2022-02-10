{-# LANGUAGE TypeOperators #-}
module Model
  where

import Data.List
import Data.Maybe
import Data.Function  -- on :: (b -> b -> c) -> (a -> b) -> a -> a -> c 
import qualified Data.PartialOrd as POrd
import qualified Data.Set as Set


import Language



-- ##################   MODEL   ########################à
-- See ModelUtility.hs  for more functions on models   

data World a = Wd(Int, Set.Set a)
  deriving (Eq, Ord, Show)


mkWorld :: Ord a => Int -> [a] -> World a
mkWorld k atms = Wd( k ,Set.fromList atms )

fmapWorld :: (Ord a ,Ord b) => (a -> b) -> (World a -> World b)
fmapWorld  f ( Wd(k, xs) ) = Wd ( k, Set.map f  xs )

worldAtms :: World a -> [a]
-- all atoms in the world
worldAtms (Wd(_,xs)) = Set.toList xs

worldInputAtms :: World Name -> [Name]
-- all atoms in the world occurring in the input formula
worldInputAtms w =
  filter (not . isNewName) (worldAtms w)

worldSetAtms :: World a -> Set.Set a
worldSetAtms (Wd(_,xs)) = xs

worldIndex :: World a -> Int
worldIndex (Wd(k,_) ) = k




data Model a = Mod( [World a ] ) 
  deriving (Show)



instance Ord a => POrd.PartialOrd (World a)  where
  (<=) (Wd(k1,s1)) (Wd(k2,s2)) = Set.isSubsetOf s1 s2
  (<)  (Wd(k1,s1)) (Wd(k2,s2)) = Set.isProperSubsetOf s1 s2



  
-- forcing/non forcing  
infixr 8 .|--.     -- world |-- atom
infixr 8 .|-/-.    -- world |-/- atom

infixr 8 .|==.    -- (model,world) |--  a :-> b
infixr 8 .|=/=.   -- (model,world) |-/- a :-> b

  
-- (.==.) :: Ord a =>  World a -> World a -> Bool
-- (.==.)  = (POrd.==) 
  
-- (./=.) :: Ord a =>  World a -> World a -> Bool
-- (./=.)  = (POrd./=) 
  

(.<.) :: Ord a =>  World a -> World a -> Bool
(.<.)  = (POrd.<) 

(.<=.) :: Ord a =>  World a -> World a -> Bool
(.<=.)  = (POrd.<=) 

(.>.) :: Ord a =>  World a -> World a -> Bool
(.>.)  = (POrd.<) 

(.>=.) :: Ord a =>  World a -> World a -> Bool
(.>=.)  = (POrd.>=) 

-- forcing

(.|--.) ::  Ord a =>  World a -> a -> Bool
w  .|--.    p = Set.member p $ worldSetAtms w 

(.|-/-.) ::  Ord a =>  World a -> a -> Bool
w .|-/-. p =  not $ w  .|--. p

(.|==.) ::  Ord a =>   (Model a, World a) ->    (a :-> a) -> Bool
(mod,w) .|==.  (a :-> b)  =
  null [ w' |  w' <-  worlds mod   ,   w  .<=.  w' ,   w' .|--. a ,   w'  .|-/-.  b  ]


(.|=/=.) ::  Ord a =>   (Model a, World a) ->    (a :-> a) -> Bool
(mod,w) .|=/=. ic = not $ (mod,w)  .|==. ic





isEmptyModel :: Model a -> Bool
isEmptyModel (Mod ws) = null ws


worlds ::  Model a -> [World a ] 
worlds (Mod ws) = ws

mkModel :: [World a ] -> Model a
mkModel ws = Mod ws


fmapModel :: (Ord a ,Ord b) => (a -> b) -> (Model a -> Model b)
fmapModel  f ( Mod ws ) = Mod (  map (fmapWorld f)  ws )




emptyModel :: Model a --Lit
emptyModel = Mod []

addWorld ::Ord a =>  World a -> Model a -> Model a
addWorld w (Mod ws) = Mod $  w : ws




--- Relarton between worlds
-- infixr 8 .==.   --  equal
-- infixr 8 ./=.   -- not  equal
infixr 8 .<.   --  less      relation between worlds
infixr 8 .<=.   -- lessEq    relation between worlds
infixr 8 .>.   --  greater   relation between worlds
infixr 8 .>=.   -- greaterEq relation between worlds




maxWorlds  :: Ord a =>  Model a -> [World a ]
-- get all the maximal worlds of a model
maxWorlds mod = POrd.maxima $ worlds mod


maxWorlds_w  :: Ord a =>  World a ->  Model a   ->  [ World a ]
-- get the maximal worlds w_max such that w <= w_max
maxWorlds_w  w mod  =
  POrd.maxima  [ w'  | w' <-  worlds mod ,  w .<=. w' ]
 
immediateSuccList_w :: Ord a => World a -> Model a -> [World a]
-- list of  the immediate successors of w in the model mod 
immediateSuccList_w w mod =
  let greater_than_w = [ w' | w' <- worlds mod , w .<. w' ]
  in   POrd.minima greater_than_w

isMaximalWorld :: Ord a => World a -> Model a -> Bool
isMaximalWorld w mod = null $immediateSuccList_w w mod

root mod = head $  POrd.minima $ worlds mod


sortWorlds ::  Ord a =>  [World a] -> [World a]
-- sort the worlds. If w1 and w2 are not comparable, we set w1 < w2 (default value in fromMaybe)
sortWorlds   = sortBy  (\w1 w2 -> fromMaybe (LT) $ POrd.compare w1 w2) 



sizeModel :: Model a -> Int 
sizeModel mod = length ( worlds mod)


realizes :: Ord a =>   (Model a, World a) -> ImplClause a -> Bool
realizes (mod,w) ((a :-> b) :-> c) =
   w  .|--.   a   ||  w  .|--.  b  ||   w   .|--. c  ||  (mod,w)   .|=/=.  (a :-> b)  


worldDifference ::  Ord a => World a -> World a -> Maybe a
-- return   p such that  p in w1 and    p  not in w2
worldDifference w1 w2 =
  let diffSet =   (worldSetAtms w1)  `Set.difference`    (worldSetAtms w2)
  in
  if Set.null diffSet then  Nothing else  Just $ Set.elemAt 0  diffSet


                                          
worldAtmDifference ::  Ord a => World a -> World a -> Form a
-- return atom p  such that  w1 |-- p  and    w2 |-/- p
-- ASSUMPTION: w1 and w2 are different
-- If w1 == w2,   fromJust fails (runtime error)
worldAtmDifference w1 w2 =
  Atom $  fromJust $ worldDifference w1 w2



lastAddedWorld ::   Ord a => Model a -> World a
lastAddedWorld mod =
  let ws =  worlds mod
      k = maxList $ map  worldIndex  ws
  in fromJust $ find (\w  -> worldIndex w == k) ws    


maxList :: Ord a => [a] -> a
-- maximal element of a list
maxList = foldr1 (\x y ->if x >= y then x else y)


getMaximalLengthChainFromWorld :: Ord a =>  World a -> Model a -> [World a]
-- get a chain of maximal length from world w0, where:
-- chain: list of worlds [w0 .. wn] such that w0 < ... < wn 
getMaximalLengthChainFromWorld w0 mod =
 if  isMaximalWorld w0 mod then [w0]
 else
   let succs = immediateSuccList_w w0 mod 
       chains = map   ( flip  getMaximalLengthChainFromWorld  mod) succs
       -- chains: chains starting from the immediate successors of  w0
       maxChain =  maximumBy (compare `on` length) chains 
   in  w0 : maxChain




