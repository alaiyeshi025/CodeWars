{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Kata.AdditionCommutes where

-- These are some lemmas that may be helpful.
-- They will *not* be tested, so rename them
-- if you so desire. Good luck!

-- | For any n, n = n.
reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS (reflexive n)

-- | if a = b, then b = a.
symmetric :: Equal a b -> Equal b a
symmetric EqlZ = EqlZ
symmetric (EqlS nm) = EqlS (symmetric nm)

-- | if a = b and b = c, then a = c.
transitive :: Equal a b -> Equal b c -> Equal a c
transitive EqlZ n = n
transitive n EqlZ = n
transitive (EqlS ab) (EqlS bc) = EqlS (transitive ab bc)

assoc :: Natural a -> Natural b -> Equal (a :+: S b) (S (a :+: b))
assoc NumZ NumZ = EqlS EqlZ
assoc NumZ (NumS m) = EqlS (assoc NumZ m)
assoc (NumS n) m = EqlS (assoc n m)

-- This is the proof that the kata requires.
-- | a + b = b + a
plusCommutes :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusCommutes NumZ NumZ = EqlZ
plusCommutes NumZ (NumS m) = EqlS (plusCommutes NumZ m)
plusCommutes (NumS n) NumZ = EqlS (plusCommutes n NumZ)
plusCommutes n (NumS m) = transitive (assoc n m) (EqlS (plusCommutes n m))
--plusCommutes n m = transitive (reflexive n) (reflexive m)
--plusCommutes (NumS n) (NumS m) = (plusNat n m) (plusNat m n)

-- For reference, here are the definitions, if you
-- want to copy them into an IDE:

-- | The natural numbers, encoded in types.
data Z
data S n

-- | Predicate describing natural numbers.
-- | This allows us to reason with `Nat`s.
data Natural :: * -> * where
    NumZ :: Natural Z
    NumS :: Natural n -> Natural (S n)
numOne = NumS NumZ
numTwo = NumS numOne
-- | Predicate describing equality of natural numbers.
data Equal :: * -> * -> * where
    EqlZ :: Equal Z Z
    EqlS :: Equal n m -> Equal (S n) (S m)

-- | Peano definition of addition.
type family (:+:) (n :: *) (m :: *) :: *
type instance Z :+: m = m
type instance S n :+: m = S (n :+: m)
