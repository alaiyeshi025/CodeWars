{-# LANGUAGE ScopedTypeVariables, Rank2Types #-}
module ScottEncoding where

import Prelude hiding (null, length, map, foldl, foldr, take, fst, snd, curry, uncurry, concat, zip, (++))

newtype SMaybe a = SMaybe { runMaybe :: forall b. b -> (a -> b) -> b }
newtype SList a = SList { runList :: forall b. b -> (a -> SList a -> b) -> b }
newtype SEither a b = SEither { runEither :: forall c. (a -> c) -> (b -> c) -> c }
newtype SPair a b = SPair { runPair :: forall c. (a -> b -> c) -> c }

toPair :: SPair a b -> (a,b)
toPair (SPair f) = f (,)

fromPair :: (a,b) -> SPair a b
fromPair (a,b) = SPair$(\g->g a b)

fst :: SPair a b -> a
fst (SPair f) = f const

snd :: SPair a b -> b
snd (SPair f) = f$flip const

swap :: SPair a b -> SPair b a
swap p = fromPair (snd p, fst p)

curry :: (SPair a b -> c) -> (a -> b -> c)
curry f = (\a b -> f (fromPair (a,b)))

uncurry :: (a -> b -> c) -> (SPair a b -> c)
uncurry f = (\p -> (runPair p) f)

toMaybe :: SMaybe a -> Maybe a
toMaybe (SMaybe f) = f Nothing Just

fromMaybe :: Maybe a -> SMaybe a
fromMaybe ma = SMaybe$(\b f -> maybe b f ma)

isJust :: SMaybe a -> Bool
isJust m = case toMaybe m of
             Nothing -> False
             Just _ -> True

isNothing :: SMaybe a -> Bool
isNothing = not.isJust

catMaybes :: SList (SMaybe a) -> SList a
catMaybes sma = foldr (\x y->case toMaybe x of
                               Nothing -> y
                               Just a -> cons a y)
                nullSList sma

toEither :: SEither a b -> Either a b
toEither (SEither se) = se Left Right

fromEither :: Either a b -> SEither a b
fromEither se = SEither$(\l r -> either l r se)

isLeft :: SEither a b -> Bool
isLeft se = case toEither se of
              Left _ -> True
              Right _ -> False

isRight :: SEither a b -> Bool
isRight = not.isLeft

partition :: SList (SEither a b) -> SPair (SList a) (SList b)
partition seab = fromPair (foldr (\x y -> case toEither x of
                                            Left a -> cons a y
                                            _ -> y)
                           nullSList seab,
                           foldr (\x y -> case toEither x of
                                            Right b -> cons b y
                                            _ -> y)
                           nullSList seab)

toList :: SList a -> [a]
toList (SList s) = s [] (\a sa -> a:(toList sa))

fromList :: [a] -> SList a
fromList [] = SList$(\a f->a)
fromList (x:xs) = SList$(\a f-> f x (fromList xs))

cons :: a -> SList a -> SList a
cons a sf = SList$(\b g -> g a sf)

nullSList :: SList a
nullSList = SList$(\a f->a)

tailSList :: SList a -> SList a
tailSList sa = case null sa of
                 True -> error "Empty SList"
                 _ -> fromList (tail (toList sa))

headSList :: SList a -> a
headSList sa = case null sa of
                 True -> error "Empty SList"
                 _ -> head (toList sa)

concat :: SList a -> SList a -> SList a
concat sa sb = case null sa of
                 True -> sb
                 _ -> cons (headSList sa) (concat (tailSList sa) sb)

null :: SList a -> Bool
null sl = case toList sl of
            [] -> True
            _ -> False

length :: SList a -> Int
length sa = case null sa of
              True -> 0
              _ -> 1+(length (tailSList sa))

map :: (a -> b) -> SList a -> SList b
map f sa = case null sa of
             True -> nullSList
             _ -> cons (f (headSList sa)) (map f (tailSList sa))

zip :: SList a -> SList b -> SList (SPair a b)
zip sa sb
    | (null sa) || (null sb) = nullSList
    | otherwise = cons (fromPair (headSList sa,headSList sb)) (zip (tailSList sa) (tailSList sb))

foldl :: (b -> a -> b) -> b -> SList a -> b
foldl f start sa = case null sa of
                     True -> start
                     _ -> foldl f (f start (headSList sa)) (tailSList sa)

foldr :: (a -> b -> b) -> b -> SList a -> b
foldr f start sa = case null sa of
                     True -> start
                     _ -> f (headSList sa) (foldr f start (tailSList sa))

take :: Int -> SList a -> SList a
take n sa
    | n == 0 = nullSList
    | n >= (length sa) = sa
    | otherwise = cons (headSList sa) (take (n-1) (tailSList sa))
