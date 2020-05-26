{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Counting where
import Data.Proxy
import Data.Void
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Sum
import Data.Functor.Product
import Data.Functor.Compose

data Nat = Z | S Nat deriving (Show, Eq, Ord)
instance Num Nat -- so (2 :: Nat) == S (S Z)
instance Enum Nat -- so ([0..3] :: [Nat]) == [Z, S Z, S (S Z)]
instance Real Nat
instance Integral Nat -- so (2 ^ 3 :: Nat) == S (S (S (S (S (S (S (S Z)))))))
{- in Preloaded:
data Nat = Z | S Nat deriving (Show, Eq, Ord)
instance Num Nat -- so (2 :: Nat) == S (S Z)
instance Enum Nat -- so ([0..3] :: [Nat]) == [Z, S Z, S (S Z)]
instance Real Nat
instance Integral Nat -- so (2 ^ 3 :: Nat) == S (S (S (S (S (S (S (S Z)))))))
-}
inf :: Nat
inf = S inf

newtype Count x = Count { getCount :: Nat } deriving (Show, Eq, Ord)

-- | helper functions
mapC :: (Nat -> Nat) -> Count x -> Count y
mapC f (Count x) = Count $ f x

liftC2 :: (Nat -> Nat -> Nat) -> Count x -> Count y -> Count z
liftC2 op (Count x) (Count y) = Count $ x `op` y

coerceC :: Count a -> Count b
coerceC (Count n) = Count n

-- | Countable
class Countable c where
  count' :: Proxy c -> Count c
  count' Proxy = count
  count :: Count c
  count = count' Proxy
  -- if you are using `Proxy` implement `count` from `count'` and vice versa
  -- count' :: Proxy c -> Count c
  -- count' = error "from count"

instance Countable Void where count = Count (0 :: Nat)
instance Countable () where count = Count (1 :: Nat) 
instance Countable Bool where count = Count (2 :: Nat)
instance Countable Nat where count = Count inf

-- | Factor
class Factor f where
    factor' :: Proxy f -> Count c -> Count (f c) 
    factor' Proxy c = factor c
    factor :: Count c -> Count (f c)
    factor = factor' Proxy
  -- factor' :: Proxy f -> Count c -> Count (f c) -- optional

instance (Factor f, Countable c) => Countable (f c) where
  count = factor count

instance Factor Maybe where factor = mapC (+(1 :: Nat))
instance Factor Identity where factor = mapC id
instance Factor Proxy where factor = mapC (const (1 :: Nat))
instance Factor Count where factor c = Count inf
instance Factor [] where factor (Count n) = if n == (0 :: Nat) then Count (1 :: Nat) else Count inf 
instance Countable c => Factor (Const c) where factor (Count n)= coerceC (count ::Count c)
instance Countable c => Factor (Either c) where factor (Count n) = Count (n + (getCount (count :: Count c)))
instance Countable c => Factor ((,) c) where factor (Count n) = Count (n * (getCount (count :: Count c)))
instance Countable c => Factor ((->) c) where factor (Count n) = Count (n ^ (getCount (count :: Count c)))
instance (Factor f, Factor g) => Factor (Sum f g) where factor (c::Count c) = liftC2 (+) (factor c :: Count (f c)) (factor c :: Count (g c))
instance (Factor f, Factor g) => Factor (Product f g) where factor (c :: Count c) = liftC2 (*) (factor c :: Count (f c)) (factor c :: Count (g c))
instance (Factor f, Factor g) => Factor (Compose f g) where factor (c :: Count c) = coerceC (factor (factor c :: Count (g c)) :: Count (f (g c)))


-- | Listable
class Countable a => Listable a where
  list :: [a]
  list = list' Proxy
  list' :: Proxy a -> [a] -- optional
  list' Proxy = list
-- Data.List.genericLength (list :: [a]) `shouldBe` getCount (count :: Count a)

instance Listable Void where list = []
instance Listable () where list = [()]
instance Listable Bool where list = [True, False]
instance Listable Nat where list = Z:(map S list)

instance Listable c => Listable (Maybe c) where list = Nothing : map Just list
instance Listable c => Listable [c] where
    list = [] : do
             x <- list :: [c]
             map (x :) (list :: [[c]])
instance (Listable a, Listable b) => Listable (Either a b) where list = map Left list ++ map Right list
instance (Listable a, Listable b) => Listable (a, b) where list = do
                                                             x <- list :: [a]
                                                             map ((x,)) (list ::[b])

instance (Eq a, Listable a, Listable b) => Listable (a -> b) where
  list = foldl (\fs x -> do
                  y <- list :: [b]
                  map (\f -> (\z -> if z == x then y else f z)) fs) [undefined] (list :: [a])

