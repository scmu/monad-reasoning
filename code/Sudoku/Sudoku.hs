module Sudoku where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.ST
import Data.Array.ST
import ListT

import Monad (guardM, ifM)
import SudoM

sudoku :: [[Int]] -> SudoM s [[Int]]
sudoku puzzle =
  initState puzzle >>= solve

side :: MonadPlus m => m a -> m b
side m = m >>= const mzero

solve :: Int -> SudoM s [[Int]]
solve 0 = gridToList
solve n = liftList [1..size] >>= \x ->
          guardM (safe x) >>
          (side (next x) `mplus`
           solve (n-1) `mplus`
           side prev)

--
runSudoku :: [[Int]] -> [[[Int]]]
runSudoku puzzle =
  fst (runST $
     newArray ((0,0), (size-1, size-1)) 0 >>= \grid ->
     runReaderT (runStateT (runListT' (sudoku puzzle)) ([],[])) grid)


-- Sample puzzles
-- Source: http://elmo.sbs.arizona.edu/sandiway/sudoku/examples.html

-- Arizona Daily Wildcat: Tuesday, Jan 17th 2006

wildcatjan17 :: [[Int]]
wildcatjan17 =
  [[0,0,0,2,6,0,7,0,1],
   [6,8,0,0,7,0,0,9,0],
   [1,9,0,0,0,4,5,0,0],
   [8,2,0,1,0,0,0,4,0],
   [0,0,4,6,0,2,9,0,0],
   [0,5,0,0,0,3,0,2,8],
   [0,0,9,3,0,0,0,7,4],
   [0,4,0,0,5,0,0,3,6],
   [7,0,3,0,1,8,0,0,0]]

-- Daily Telegraph January 19th "Diabolical"

dtfeb19 :: [[Int]]
dtfeb19 =
  [[0,2,0,6,0,8,0,0,0],
   [5,8,0,0,0,9,7,0,0],
   [0,0,0,0,4,0,0,0,0],
   [3,7,0,0,0,0,5,0,0],
   [6,0,0,0,0,0,0,0,4],
   [0,0,8,0,0,0,0,1,3],
   [0,0,0,0,2,0,0,0,0],
   [0,0,9,8,0,0,0,3,6],
   [0,0,0,3,0,6,0,9,0]]

-- Vegard Hanssen puzzle 2155141

v2155141 :: [[Int]]
v2155141 =
  [[0,0,0,6,0,0,4,0,0],
   [7,0,0,0,0,3,6,0,0],
   [0,0,0,0,9,1,0,8,0],
   [0,0,0,0,0,0,0,0,0],
   [0,5,0,1,8,0,0,0,3],
   [0,0,0,3,0,6,0,4,5],
   [0,4,0,2,0,0,0,6,0],
   [9,0,3,0,0,0,0,0,0],
   [0,2,0,0,0,0,1,0,0]]
