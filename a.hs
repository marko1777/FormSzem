module Hf7 where

digits :: Integer -> [Integer]

digits x 
    | x < 10 = [mod x 10]
    | otherwise = (mod x 10) : digits (div x 10)

squareSum :: [Integer] -> Integer

squareSum l = sum (map (\x -> x^2) l)

happy :: Integer -> Bool

happy x
    | squareSum (digits x) == 1 = True
    | squareSum (digits x) == 0 = False
    | otherwise = happy (squareSum (digits x))