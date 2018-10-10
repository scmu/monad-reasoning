module SudoM where

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.ST
import Data.Array.ST
import Data.Array.IArray
import Data.List (partition)
import ListT

import Debug.Trace

type Pos = (Int, Int)
type Entry = Int
type Grid s = STUArray s Pos Entry
type PosZ = ([Pos], [Pos])

type SudoM s = ListT (StateT PosZ (ReaderT (Grid s) (ST s)))

-- see http://stackoverflow.com/questions/23579959/how-to-put-mutable-vector-into-state-monad

runListT' :: (Monad m) => ListT m a -> m [a]
runListT' = foldListT cons (return [])
    where cons x m = (x:) <$> m

size, bsize :: Int
size  = 9
bsize = 3

writeGrid :: Pos -> Int -> SudoM s ()
writeGrid i e = writeGrid_ i e =<< ask

writeGrid_ :: Pos -> Int -> Grid s -> SudoM s ()
writeGrid_ i e grid = lift . lift . lift $ writeArray grid i e


readGrid :: Pos -> SudoM s Int
readGrid i = readGrid_ i =<< ask

readGrid_ :: Pos -> Grid s -> SudoM s Int
readGrid_ i grid = lift . lift . lift $ readArray grid i

initState :: [[Int]] -> SudoM s Int
initState conf =
    put (map fst empties, []) >>
    ask >>= addEntries given >>
    return (length empties)
  where entries = concat . addPoss $ conf
        (given, empties) = partition ((0 /=) . snd) entries
        addEntries [] _ = return ()
        addEntries (((x,y),e):xs) grid =
            writeGrid_ (x,y) e grid >> addEntries xs grid

addPoss :: [[a]] -> [[(Pos, a)]]
addPoss xss = map addX (zipWith addY [0..] xss)
   where addY y = map (\e -> (y,e))
         addX = zipWith (\x (y,e) -> ((x,y),e)) [0..]

safe :: Int -> SudoM s Bool
safe e = get >>= \(i:_, _) ->
         ask >>= noCollision e (collisions ! i)
 where noCollision _ []     _     = return True
       noCollision e (i:is) grid =
           readGrid_ i grid >>= \e' ->
           if e == e' then return False
             else noCollision e is grid


next :: Int -> SudoM s ()
next e = get   >>= \(i:is, js) ->
         -- trace ("next : " ++ show (e,i))
         (writeGrid i e >> put (is, i:js))

prev :: SudoM s ()
prev = get   >>= \(is, i:js) ->
       writeGrid i 0 >> put (i:is, js)

gridToList :: SudoM s [[Int]]
gridToList = ask >>= \grid ->
              mapM (mapM (flip readGrid_ grid)) coords
 where coords = [[(i,j) | i <- [0..size-1]] | j <- [0..size-1]]

unsolved :: SudoM s Bool
unsolved = (not . null . fst) <$> get

--

row, col, box :: Pos -> [Pos]
row (_,y) = map (\i -> (i,y)) [0..size-1]
col (x,_) = map (\i -> (x,i)) [0..size-1]
box (x,y) = [(i,j) | i <- [xi..xi+bsize-1],
                     j <- [yi..yi+bsize-1]]
   where xi = (x `div` bsize) * bsize
         yi = (y `div` bsize) * bsize

collisions :: Array Pos [Pos]
collisions =
   array ((0,0), (size-1, size-1))
    [((x,y), f (x,y))| x <- [0..size-1], y <- [0..size-1]]
 where f i = filter (i/=) (row i ++ col i ++ box i)
