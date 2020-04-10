{-# LANGUAGE NoImplicitPrelude, GADTs , DataKinds, TypeFamilies, TypeOperators, RankNTypes, DeriveFunctor #-}

module Singletons where

import Prelude hiding (drop, take, head, tail, index, zipWith, replicate, map, (++))

data Vec a n where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

-- promoted to type level by data kinds
data Nat = Zero | Succ Nat

data SNat a where
  SZero :: SNat Zero
  SSucc :: SNat a -> SNat (Succ a)

type family (a :: Nat) :< (b :: Nat) :: Bool
type instance m :< Zero = False
type instance Zero :< Succ n = True
type instance (Succ m) :< (Succ n) = m :< n

type family (a :: Nat) := (b :: Nat) :: Bool
type instance Zero := Zero = True
type instance (Succ m) := Zero = False
type instance Zero := (Succ m) = False
type instance (Succ m) := (Succ n) = m := n

type family (a :: Nat) :- (b :: Nat) :: Nat
type instance Zero :- m = Zero
type instance m :- Zero = m
type instance (Succ m) :- (Succ n) = m :- n

type family (Add (a :: Nat) (b :: Nat)) :: Nat
type instance Add Zero m = m
type instance Add (Succ m) n = Succ (Add m n)

type family (Min (a :: Nat) (b :: Nat)) :: Nat
type instance Min Zero n = Zero
type instance Min n Zero = Zero
type instance Min (Succ m) (Succ n) = Succ (Min m n)
    
map :: (a -> b) -> Vec a n -> Vec b n
map f VNil = VNil
map f (VCons x xs) = VCons (f x) (map f xs)

index :: ((a :< b) ~ True) => SNat a -> Vec s b -> s
index SZero (VCons x xs) = x
index (SSucc n) (VCons x xs) = index n xs

replicate :: s -> SNat a -> Vec s a
replicate _ SZero = VNil
replicate s (SSucc n) = VCons s (replicate s n)

-- Both vectors must be of equal length
zipWith :: ((n1 := n2) ~ True) => (s1 -> s2 -> s3) -> (Vec s1 n1) -> (Vec s2 n2) -> (Vec s3 n1)
zipWith f (VCons x xs) (VCons y ys) = (VCons (f x y) (zipWith f xs ys))
zipWith f VNil VNil = VNil
                      
(++) :: Vec v m -> Vec v n -> Vec v (Add m n)
VNil ++ b = b
(VCons x xs) ++ b = (VCons x (xs ++ b))

-- The semantics should match that of take for normal lists.
take :: SNat a -> Vec s b -> Vec s (Min a b)
take SZero _ = VNil
take (SSucc n) VNil = VNil
take (SSucc n) (VCons x xs) = (VCons x (take n xs))

-- The semantics should match that of drop for normal lists.
drop :: SNat a -> Vec s b -> Vec s (b :- a)
drop SZero v = v
drop n VNil = VNil
drop (SSucc n) (VCons x xs) = drop n xs

head :: ((Zero :< n) ~ True) => Vec s n -> s
head (VCons x xs) = x

tail :: ((Zero :< n) ~ True) => Vec s n -> Vec s (n :- (Succ Zero))
tail (VCons x xs) = xs
