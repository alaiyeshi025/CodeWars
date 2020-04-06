{-# LANGUAGE DeriveFunctor #-}
module Coroutine where

import Control.Monad (ap, forever)

newtype Coroutine r u d a = Coroutine { runCoroutine :: (Command r u d a -> r) -> r } deriving (Functor)

data Command r u d a =
    Done a
    | Out d (Coroutine r u d a)
    | In (u -> Coroutine r u d a) deriving Functor

-- Useful alias
apply :: Coroutine r u d a -> (Command r u d a -> r) -> r
apply = runCoroutine

instance Applicative (Coroutine r u d) where
  pure = return
  (<*>) = ap

instance Monad (Coroutine r u d) where
  return x = Coroutine (\k -> k (Done x))
  f >>= g  = Coroutine (\k -> apply f (\h -> case h of
                                               (Done a) -> apply (g a) k
                                               (Out d c) -> k (Out d (c >>= g))
                                               (In uruda) -> k (In (fmap (>>= g) uruda))))

(>>>) :: Coroutine r u m a -> Coroutine r m d a -> Coroutine r u d a
p1 >>> p2 = Coroutine (\k -> apply p2 (\h -> case h of
                                               (Done a) -> k (Done a)
                                               (Out d c) -> k (Out d (p1 >>> c))
                                               (In mrmda) -> apply (pipe2 p1 mrmda) k))

-- It might be useful to define the following function
pipe2 :: Coroutine r u m a -> (m -> Coroutine r m d a) -> Coroutine r u d a
pipe2 p mf = Coroutine (\k -> apply p (\h -> case h of
                                               (Done a) -> k (Done a)
                                               (Out m c) -> apply (c >>> (mf m)) k
                                               (In uruma) -> k (In (fmap (\c-> pipe2 c mf) uruma))))

-- Library functions
output :: a -> Coroutine r u a ()
output v = Coroutine (\k -> k (Out v (pure ())))

input :: Coroutine r v d v
input = Coroutine (\k -> k (In (\v -> return v)))

produce :: [a] -> Coroutine r u a ()
produce [] = return ()
produce (x:xs) = (output x) >>= (\dummy -> produce xs)

consume :: Coroutine [t] u t a -> [t]
consume c = apply c (\h -> case h of
                             (Out d cn) -> d:(consume cn)
                             otherwise -> [])

filterC :: (v -> Bool) -> Coroutine r v v ()
filterC p = forever (input >>= (\v -> if (p v)
                                      then (output v)
                                      else (return ())))

limit :: Int -> Coroutine r v v ()
limit n = if n <= 0
          then return ()
          else (input >>= output) >>= (\dummy -> limit (n-1))

suppress :: Int -> Coroutine r v v ()
suppress n = forever (input >>= (\v -> case n of
                                         0 -> (output v)
                                         otherwise -> ((return ()) >>= (\dummy -> (suppress (n-1))))))

add :: Coroutine r Int Int ()
add = forever (input >>= (\v1 -> input >>= (\v2 -> output (v1+v2))))

duplicate :: Coroutine r v v ()
duplicate = forever (input >>= (\v -> output v >>= (\dummy -> output v)))

-- Programs
-- 1. A program which outputs the first 5 even numbers of a stream.
-- 2. A program which produces a stream of the triangle numbers 
-- 3. A program which multiplies a stream by 2
-- 4. A program which sums adjacent pairs of integers

p1, p2, p3, p4 :: Coroutine r Int Int ()

p1 = (filterC even) >>> (limit 5)
p2 = produce [ x * (x + 1) `div` 2 | x <- [1 ..] ]
p3 = duplicate >>> add
p4 = duplicate >>> suppress 1 >>> add
