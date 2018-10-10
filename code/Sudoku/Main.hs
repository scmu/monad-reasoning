module Main where

import Data.Char
import Sudoku

main :: IO ()
main = (readPuzzle . tidyup . lines <$> getContents) >>= \puzzle ->
       printBoard (head (runSudoku puzzle))


tidyup :: [String] -> [String]
tidyup = filter (not . null) .
         map (filter (not . isSpace)) .
         filter (("--" /=) . take 2)

readPuzzle :: [String] -> [[Int]]
readPuzzle = map readRow

readRow :: String -> [Int]
readRow [] = []
readRow (x:xs) = (ord x - ord '0') : readRow xs

printBoard :: [[Int]] -> IO ()
printBoard [] = return ()
printBoard (xs:xss) = mapM putDigit xs >>
                      putChar '\n' >>
                      printBoard xss
  where putDigit d = putChar (chr (d + ord '0')) >> putChar ' '
