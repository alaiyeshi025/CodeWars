{-# LANGUAGE
  FlexibleInstances,
  UndecidableInstances,
  InstanceSigs,
  ScopedTypeVariables,
  RankNTypes #-}

module PC where

import Data.List

type ISO a b = (a -> b, b -> a)
-- See https://www.codewars.com/kata/isomorphism

symm :: ISO a b -> ISO b a
symm (ab, ba) = (ba, ab)

substL :: ISO a b -> (a -> b)
substL = fst

substR :: ISO a b -> (b -> a)
substR = snd

liftISO2 :: ISO a b -> ISO (a -> a -> a) (b -> b -> b)
liftISO2 ab =( \fa-> \b1-> \b2-> (fst ab) (fa ((snd ab) b1) ((snd ab) b2)),
               \fb-> \a1-> \a2-> (snd ab) (fb ((fst ab) a1) ((fst ab) a2)))

liftF :: ISO n p -> ISO (n->a) (p->a)
liftF np = (\na -> \p -> na ((snd np) p),
            \pa -> \n -> pa ((fst np) n))

-- A Natural Number is either Zero,
-- or a Successor (1 +) of Natural Number.
-- We have (+)/(*) on Natural Number, or (-) it.
-- Since Natrual Number do not have negative, forall x, 0 - x = 0.
-- We also have pow on Natrual Number
-- Since Haskell is lazy, we also have infinity

class Nat n where
  zero :: n
  successor :: n -> n
  nat :: a -> (n -> a) -> n -> a -- Pattern Matching
  iter :: a -> (a -> a) -> n -> a -- Induction
  plus, minus, mult, pow :: n -> n -> n
  inf :: n
  inf = successor inf
  divide :: n -> n -> n
  l `divide` r | l == 0 && r == 0 = undefined
  l `divide` r | l < r = 0
  l `divide` r | otherwise = successor $ (l `minus` r) `divide` r
  -- notice (l `divide` 0) when l is not 0 will return inf
  isoP :: ISO n Peano -- See below for the definition of Peano
  isoP = (iter zero successor, iter zero successor)
  toP :: n -> Peano
  toP = substL isoP

instance {-# OVERLAPPABLE #-} Nat n => Show n where
  show = show . toP

instance {-# OVERLAPPABLE #-} Nat n => Eq n where
  l == r = toP l == toP r

instance {-# OVERLAPPABLE #-} Nat n => Ord n where
  l `compare` r = toP l `compare` toP r

instance {-# OVERLAPPABLE #-} Nat n => Num n where
  abs = id
  signum = nat zero (const 1)
  fromInteger 0 = zero
  fromInteger n | n > 0 = successor $ fromInteger (n - 1)
  (+) = plus
  (*) = mult
  (-) = minus

-- We can encode Natrual Number directly as Algebraic Data Type(ADT).
data Peano = O | S Peano deriving (Show, Eq, Ord)

-- Remember, 0 - x = 0 for all x.
instance Nat Peano where
  zero = O

  successor = S

  nat dft f O = dft
  nat dtf f (S n) = f n

  iter start f O = start
  iter start f (S n) = iter (f start) f n

  plus n1 n2 = iter n1 successor n2

  minus O _ = O
  minus n1 O = n1
  minus (S n1) (S n2) = minus n1 n2

  mult O _ = O
  mult _ O = O
  mult n1 (S n2) = iter n1 (plus n1) n2

  pow _ O = S O
  pow O _ = O
  pow n1 (S n2) = iter n1 (mult n1) n2
-- Peano is very similar to a basic data type in Haskell - List!
-- O is like [], and S is like :: (except it lack the head part)
-- When we want to store no information, we can use (), a empty tuple
-- This is different from storing nothing (called Void in Haskell),
-- as we can create a value of () by using (),
-- but we cannot create a value of Void.

-- Notice how you can implement everything once you have isoP,
-- By converting to Peano and using Nat Peano?
-- Dont do that. You wont learn anything.
-- Try to use operation specific to list.
instance Nat [()] where
  zero = []

  successor = (():)

  nat dft f [] = dft
  nat dft f (x:xs) =  f xs

  iter start f [] = start
  iter start f (x:xs) = iter (f start) f xs

  plus n1 n2 = iter n1 successor n2

  minus [] _ = []
  minus n1 [] = n1
  minus (x:xs) (y:ys) = minus xs ys

  mult [] _ = []
  mult _ [] = []
  mult n1 (x:xs) = iter n1 (plus n1) xs

  pow _ [] = [()]
  pow [] _ = []
  pow n1 (x:xs) = iter n1 (mult n1) xs

-- Instead of defining Nat from zero, sucessor (and get Peano),
-- We can define it from Pattern Matching
newtype Scott = Scott { runScott :: forall a. a -> (Scott -> a) -> a }
instance Nat Scott where
  -- Other operation on Scott numeral is sort of boring,
  -- So we implement it using operation on Peano.
  -- You shouldnt do this - I had handled all the boring case for you.
  plus = substR (liftISO2 isoP) plus
  minus = substR (liftISO2 isoP) minus
  mult = substR (liftISO2 isoP) mult
  pow = substR (liftISO2 isoP) pow

  zero = Scott$(\a-> \f-> a)

  successor n = Scott $ (\a-> \f-> f n)

  iter start f n = (runScott n) start $ iter (f start) f

  nat dft f n = (runScott n) dft f

-- Or from induction!
newtype Church = Church { runChurch :: forall a. (a -> a) -> a -> a }

isZero n = (runChurch n) (\y->False) True

churchToInt n = (runChurch n) (+1) 0

instance Nat Church where
  -- Try to implement the calculation (except minus) in the primitive way.
  -- Implement them by constructing Church explicitly.
  -- So plus should not use successor,
  -- mult should not use plus,
  -- exp should not use mult.
  zero = Church $ (\f-> id)

  nat dft f n
    | isZero n = dft
    | otherwise = f (fromInteger ((churchToInt n)-1))

  iter start f n = (runChurch n) f start

  successor c = Church $ (\h -> h . (runChurch c) h)

  plus c1 c2 = Church $ (\f->(\x->((runChurch c1) f) ((runChurch c2) f x)))

  mult c1 c2 = Church $ (\f->(\x->(runChurch c1) ((runChurch c2) f) x))

  pow cb ce = Church $ (\f->(\x->((runChurch ce) (runChurch cb)) f x))

  minus = substR (liftISO2 isoP) minus
  
