{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module PolyvariadicFunctions where

class SumRes r where 
    sumOf :: Int -> r

instance SumRes Int where
    sumOf = id

instance (Integral a, SumRes r) => SumRes (a -> r) where
    sumOf x = sumOf . (x +) . fromIntegral

-- `polyAdd` sums its arguments, all `Int`s.
polyAdd :: (SumRes r) => r
polyAdd = (sumOf 0)

class ListRes a r | r -> a where 
    listOf :: [a] -> r

instance ListRes a [a] where
    listOf = id

instance (ListRes a r) => ListRes a (a -> r) where
    listOf x = listOf . (x++) . return 
    
-- `polyList` turns its arguments into a list, polymorphically.
polyList :: (ListRes a r) => r
polyList = listOf []

class WordRes r where 
    wordOf :: String -> r

instance WordRes [Char] where
    wordOf [] = []
    wordOf x = tail x

instance (WordRes r) => WordRes ([Char] -> r) where
    wordOf x = wordOf . ((x ++ " ") ++ ) 
    
-- `polyWords` turns its arguments into a spaced string.
polyWords :: (WordRes r) => r
polyWords = wordOf ""
