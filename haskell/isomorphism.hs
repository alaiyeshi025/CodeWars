module ISO where

-- Please copy your code of Isomorphism to here.
import Data.Void
import Data.Maybe
import Data.Either
import Data.Tuple
import Unsafe.Coerce

type ISO a b = (a -> b, b -> a)

substL :: ISO a b -> (a -> b)
substL = fst

substR :: ISO a b -> (b -> a)
substR = snd

isoBool :: ISO Bool Bool
isoBool = (id, id)

isoBoolNot :: ISO Bool Bool
isoBoolNot = (not, not)

refl :: ISO a a
refl = (id,id)

symm :: ISO a b -> ISO b a
symm = swap

trans :: ISO a b -> ISO b c -> ISO a c
trans (ab,ba) (bc,cb) = (bc.ab,ba.cb)

isoTuple :: ISO a b -> ISO c d -> ISO (a, c) (b, d)
isoTuple (ab, ba) (cd, dc) =
  (\(a, c) -> (ab a, cd c), \(b,d)->(ba b, dc d))

isoList :: ISO a b -> ISO [a] [b]
isoList (ab,ba) = ((map ab), (map ba))

isoMaybe :: ISO a b -> ISO (Maybe a) (Maybe b)
isoMaybe (ab, ba) = ((fmap ab), (fmap ba))

isoEither :: ISO a b -> ISO c d -> ISO (Either a c) (Either b d)
isoEither (ab,ba) (cd,dc) = ((either (\l->Left (ab l)) (\r->Right (cd r))), (either (\l->Left (ba l)) (\r->Right (dc r))))

isoFunc :: ISO a b -> ISO c d -> ISO (a -> c) (b -> d)
isoFunc (ab,ba) (cd,dc) = ((\f->cd.f.ba),(\f->dc.f.ab))

isoUnMaybe :: ISO (Maybe a) (Maybe b) -> ISO a b
isoUnMaybe (mab, mba) = ((\a-> case mab (Just a) of
                                Just b -> b
                                Nothing -> fromJust (mab Nothing)),
                         (\b-> case mba (Just b) of
                                Just a -> a
                                Nothing -> fromJust (mba Nothing)))

isoEU :: ISO (Either [()] ()) (Either [()] Void)
isoEU = ((\x-> case x of
                  Left ones -> Left (():ones)
                  Right one -> Left []),
         (\x-> case x of
                  Left (x:xs) -> Left xs
                  _ -> Right ()))

isoSymm :: ISO (ISO a b) (ISO b a)
isoSymm = (symm,symm)
-- Sometimes, we can treat a Type as a Number:
-- if a Type t has n distinct value, it's Number is n.
-- This is formally called cardinality.
-- See https://en.wikipedia.org/wiki/Cardinality

-- Void has cardinality of 0 (we will abbreviate it Void is 0).
-- () is 1.
-- Bool is 2.
-- Maybe a is 1 + a.
-- We will be using peano arithmetic so we will write it as S a.
-- https://en.wikipedia.org/wiki/Peano_axioms
-- Either a b is a + b.
-- (a, b) is a * b.
-- a -> b is b ^ a. Try counting (() -> Bool) and (Bool -> ())

-- Algebraic data type got the name because
-- it satisfies a lot of algebraic rules under isomorphism

-- a = b -> c = d -> a * c = b * d
isoProd :: ISO a b -> ISO c d -> ISO (a, c) (b, d)
isoProd = isoTuple

-- a = b -> c = d -> a + c = b + d
isoPlus :: ISO a b -> ISO c d -> ISO (Either a c) (Either b d)
isoPlus = isoEither

-- a = b -> S a = S b
isoS :: ISO a b -> ISO (Maybe a) (Maybe b)
isoS = isoMaybe

-- a = b -> c = d -> c ^ a = d ^ b
isoPow :: ISO a b -> ISO c d -> ISO (a -> c) (b -> d)
isoPow = isoFunc

-- a + b = b + a
plusComm :: ISO (Either a b) (Either b a)
plusComm = (either Right Left,either Right Left)

-- a + b + c = a + (b + c)
plusAssoc :: ISO (Either (Either a b) c) (Either a (Either b c))
plusAssoc = (either (either Left (Right . Left)) (Right . Right), either (Left . Left) (either (Left . Right) Right))

-- a * b = b * a
multComm :: ISO (a, b) (b, a)
multComm = (swap, swap)

-- a * b * c = a * (b * c)
multAssoc :: ISO ((a, b), c) (a, (b, c))
multAssoc = (\x->(fst.fst$x,(snd.fst$x, snd x)), \x->((fst x, fst.snd$x), snd.snd$x))

-- dist :: a * (b + c) = a * b + a * c
dist :: ISO (a, (Either b c)) (Either (a, b) (a, c))
dist = (\x-> either (\b -> Left (fst x, b)) (\c-> Right (fst x, c)) (snd x),either (\ab-> (fst ab, Left (snd ab))) (\ac-> (fst ac, Right (snd ac))))

-- (c ^ b) ^ a = c ^ (a * b)
curryISO :: ISO (a -> b -> c) ((a, b) -> c)
curryISO = (\f -> (\ab -> f (fst ab) (snd ab)), \f-> \a -> \b -> f (a,b))

-- 1 = S O (we are using peano arithmetic)
-- https://en.wikipedia.org/wiki/Peano_axioms
one :: ISO () (Maybe Void)
one = (const Nothing, const ())

-- 2 = S (S O)
two :: ISO Bool (Maybe (Maybe Void))
two = (\a->if a then Just Nothing else Nothing, maybe False (maybe True absurd))

-- O + b = b
plusO :: ISO (Either Void b) b
plusO = (left, Right)
  where
    left (Left  x) = absurd x -- absurd :: Void -> a
    left (Right x) = x

-- S a + b = S (a + b)
plusS :: ISO (Either (Maybe a) b) (Maybe (Either a b))
plusS = (either (maybe Nothing (Just . Left)) (Just . Right), maybe (Left Nothing) (either (Left . Just) Right))

-- 1 + b = S b
plusSO :: ISO (Either () b) (Maybe b)
plusSO = isoPlus one refl `trans` plusS `trans` isoS plusO

-- O * a = O
multO :: ISO (Void, a) Void
multO = (absurd.fst,absurd)

-- S a * b = b + a * b
multS :: ISO (Maybe a, b) (Either b (a, b))
multS = (\x -> maybe (Left (snd x)) (\a->Right (a, (snd x))) (fst x),
         either (\b->(Nothing,b)) (\ab->(Just (fst ab), snd ab)))

-- 1 * b = b
multSO :: ISO ((), b) b
multSO =
  isoProd one refl `trans`
    multS `trans`
    isoPlus refl multO `trans`
    plusComm `trans`
    plusO

-- a ^ O = 1
powO :: ISO (Void -> a) ()
powO = (\f->(),\x->absurd)

-- a ^ (S b) = a * (a ^ b)
powS :: ISO (Maybe b -> a) (a, b -> a)
powS = (\f-> (f Nothing, \b->f (Just b)), \af -> \mb -> maybe (fst af) (snd af) mb)

-- a ^ 1 = a
-- Go the hard way (like multSO, plusSO)
-- to prove that you really get what is going on!
powSO :: ISO (() -> a) a
powSO = isoPow one refl `trans` powS `trans` isoProd refl powO `trans` multComm `trans` multSO
--_ `trans` powS `trans` _
-- Here's a trick:
-- replace undefined with the rhs of the comment on previous line
-- When you're not sure what to fill in for a value,
-- Have it as a _
-- GHC will goes like
-- "Found hole `_' with type: ISO (() -> a) (Maybe b0 -> a0)"
-- So you can immediately see value of what type are needed
-- This process can be repeat indefinitely -
-- For example you might replace `_` with `isoFunc _ _`
-- So GHC hint you on more specific type.
-- This is especially usefull if you have complex type.
-- See https://wiki.haskell.org/GHC/Typed_holes
-- And "stepwise refinement" for more details.
