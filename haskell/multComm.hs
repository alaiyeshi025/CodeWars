{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, UndecidableInstances #-}

module Kata.TimesComm where

-- | The natural numbers, encoded in types.
data Z
data S n

-- | Predicate describing natural numbers.
-- | This allows us to reason with `Nat`s.
data Natural :: * -> * where
  NumZ :: Natural Z
  NumS :: Natural n -> Natural (S n)

-- | Predicate describing equality of natural numbers.
data Equal :: * -> * -> * where
  EqlZ :: Equal Z Z
  EqlS :: Equal n m -> Equal (S n) (S m)

-- | Peano definition of addition.
type family (:+:) (n :: *) (m :: *) :: *
type instance Z :+: m = m
type instance S n :+: m = S (n :+: m)

-- | Peano definition of multiplication.
type family (:*:) (n :: *) (m :: *) :: *
type instance Z :*: m = Z
type instance S n :*: m = m :+: (n :*: m)

-- This will be helpful
plus' :: Equal n m -> Natural a -> Equal (n :+: a) (m :+: a)
plus' EqlZ a = reflexive a
plus' (EqlS p) a = EqlS (plus' p a)

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-plus-c-equals-a-plus-b-plus-c-prove-it/haskell
plusAssoc :: Natural a -> Natural b -> Natural c -> Equal (a :+: (b :+: c)) ((a :+: b) :+: c)
plusAssoc NumZ sb sc = reflexive (plusNat sb sc)
plusAssoc (NumS a) sb sc = EqlS (plusAssoc a sb sc)

reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS (reflexive n)

plusNat :: Natural a -> Natural b -> Natural (a:+:b)
plusNat NumZ b = b
plusNat (NumS a) b = NumS (plusNat a b)

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-equals-b-plus-a-prove-it/haskell
plusComm :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusComm NumZ NumZ = EqlZ
plusComm NumZ (NumS m) = EqlS (plusComm NumZ m)
plusComm (NumS n) NumZ = EqlS (plusComm n NumZ)
plusComm n (NumS m) = transitive (assoc n m) (EqlS (plusComm n m))

transitive :: Equal a b -> Equal b c -> Equal a c
transitive EqlZ n = n
transitive n EqlZ = n
transitive (EqlS ab) (EqlS bc) = EqlS (transitive ab bc)

assoc :: Natural a -> Natural b -> Equal (a :+: S b) (S (a :+: b))
assoc NumZ NumZ = EqlS EqlZ
assoc NumZ (NumS m) = EqlS (assoc NumZ m)
assoc (NumS n) m = EqlS (assoc n m)

symmetric :: Equal a b -> Equal b a
symmetric EqlZ = EqlZ
symmetric (EqlS nm) = EqlS (symmetric nm)

-- This will also be helpful
multZero :: Natural a -> Natural (a :*: Z)
multZero NumZ = NumZ
multZero (NumS a) = multZero a

multNat :: Natural a -> Natural b -> Natural (a :*: b)
multNat NumZ sb = NumZ
multNat (NumS a) sb = plusNat sb (multNat a sb)

zeroComm :: Natural a -> Equal Z (a :*: Z)
zeroComm NumZ = EqlZ
zeroComm (NumS a) = zeroComm a

-- This is the proof that the kata requires.
-- | a * b = b * a
timesComm :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
timesComm NumZ b = zeroComm b
timesComm a NumZ = symmetric (zeroComm a)
timesComm sa@(NumS a) sb@(NumS b) = EqlS $
      plusComm b (multNat a sb)
  `transitive` plus' (timesComm a sb) b
  `transitive` symmetric (plusAssoc a (multNat b a) b)
  `transitive` plusComm a (plusNat (multNat b a) b)
  `transitive` symmetric (plusAssoc (multNat b a) b a)
  `transitive` plus' (timesComm b a) (plusNat b a)
  `transitive` plusAssoc (multNat a b) b a
  `transitive` plus' (plusComm (multNat a b) b) a
  `transitive` plus' (timesComm sa b) a
  `transitive` plusComm (multNat b sa) a
  `transitive` reflexive (plusNat a (multNat b sa))
