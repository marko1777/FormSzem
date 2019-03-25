module Hf5 where

remove :: a -> [a] -> [a]

remove a (x:xs)
    | (a == x) = xs
    | otherwise = x : remove a xs

remove a [] = []