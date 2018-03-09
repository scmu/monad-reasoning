module Utilities where

infixl 0 ===
  
(===) :: a -> a -> a
x === y = x

notelem :: Eq a => a -> [a] -> Bool
x `notelem` xs = not (x `elem` xs)
