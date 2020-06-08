-- Author: Mateusz Forc <formateu@gmail.com>
-- Latin square (Pyramids) backtracking solver

import           Control.Applicative ((<|>))
import           Data.Char           (digitToInt)
import           Data.Function       (on)
import           Data.List           (foldl', minimumBy, transpose, (\\))

-- We represent each cell on grid as a Fixed number or list of possibilities
data Cell
  = Fixed Int
  | Possible [Int]
  deriving (Show, Eq)

type Row  = [Cell]
type Grid = [Row]

showGrid :: Grid -> String
showGrid = unlines . map (unwords . map showCell)
  where
    showCell (Fixed x) = show x
    showCell _         = "."

-- For debugging purposes: Print full grid
showGridWithPossibilities :: Grid -> String
showGridWithPossibilities = unlines . map (unwords . map showCell)
  where
    showCell (Fixed x)     = show x ++ "  "
    showCell (Possible xs) =
      (++ "]")
      . foldl' (\acc x -> acc ++ if x `elem` xs then show x else " ") "["
      $ [1..4]

{- Grid generation
   We generate grid as complete list of possibilities with given problem size
-}
generateCell :: Int -> Cell
generateCell size = Possible [1..size]

generateRow :: Int -> Row
generateRow size = replicate size (generateCell size)

generateGrid :: Int -> Grid
generateGrid size = replicate size (generateRow size)

{- Input format
   Known view : number, ex. 4
   No information: 0 or .
   Example: 3.1. (Upper view from project description)
-}
readViews :: String -> [Int]
readViews = fmap readCell
    where readCell '.' = 0
          readCell c   = digitToInt c

readInt :: IO Int
readInt = do
    int <- getLine
    return (read int)

{- Possibilities Reduction with given views algorithm:
  0 - no information, do nothing
  1 - nearest field = problem size
  problem size - whole row is sorted ascending natural numbers [1..problem size]
  between 1 and problem size:
  We basically do explanation given here: https://www.wydawnictwologi.pl/zasady/tips/pomoc6.html
  Idea: Given view `k` and problem size `n` start at position k-1 and remove `n` from possibilities
        Then go left and remove n-1,n
        Repeat to row beginning
  Implementation: We start at beginning of the row and remove all numbers from [n-k+2,n]
                  In the next cell remove [n-k+2 + 1, n]..
                  Break on index `n`

-}
removeFrom :: Int -> Cell -> Cell
removeFrom toRemove (Fixed value)
    | value == toRemove = Possible []
removeFrom toRemove (Possible intList) = Possible (filter (/= toRemove) intList)

removeIncremental :: Int -> Int -> Row -> Row
removeIncremental howManyWeSee problemSize = removeGEGrowing (problemSize-howManyWeSee+2) problemSize

removeGEGrowing :: Int -> Int -> Row -> Row
removeGEGrowing h p (x:xs)
    | h <= p =  removeGE h x : removeGEGrowing (h+1) p xs
    | otherwise = x:xs

removeGEGrowing _ _ [] = []

removeGE :: Int -> Cell -> Cell
removeGE toRemove (Possible list) = Possible (takeWhile (< toRemove) list)

removeGE toRemove (Fixed n)
    | n == toRemove = Possible []
    | otherwise = Fixed n

applyViewImpl :: Int -> Int -> Row -> Row
applyViewImpl problemSize howManyWeSee (xs:ys)
    | howManyWeSee == 0 = xs:ys
    | howManyWeSee == problemSize = fmap Fixed [1..problemSize]
    | howManyWeSee == 1 = Fixed problemSize : ys
    | otherwise = removeIncremental howManyWeSee problemSize (xs:ys)

{- Reducing possibilities with given view
  In order to `apply` view on the grid we first transform lists, so we can iterate over view and properly angled grid
  left view - just apply
  upper view - transpose grid, apply, transpose again (transposition inverse itself)
  right view - transpose, reverse, transpose, apply, repeat transformation (also inverse itself)
  bottom view - transpose, reverse, apply, reverse, transpose
-}
applyView :: (Grid -> Grid) -> Int -> [Int] ->  Grid -> Grid
applyView transformFunc problemSize upperView grid = transformFunc (zipWith (applyViewImpl problemSize) upperView (transformFunc grid))

applyUpperView :: Int -> [Int] -> Grid -> Grid
applyUpperView = applyView transpose

applyLeftView :: Int -> [Int] -> Grid -> Grid
applyLeftView  = applyView id

applyRightView :: Int -> [Int] -> Grid -> Grid
applyRightView = applyView (transpose . reverse . transpose)

applyBottomView :: Int -> [Int] -> Grid -> Grid
applyBottomView problemSize bottomView grid = transpose $ reverse (zipWith (applyViewImpl problemSize) bottomView . reverse . transpose $ grid)

{- Remove fixed values from possibilities lists in given Row
-}
pruneCells :: Row -> Maybe Row
pruneCells cells = traverse pruneCell cells
  where
    fixeds = [x | Fixed x <- cells]

    pruneCell (Possible xs) = case xs \\ fixeds of
      []  -> Nothing
      [y] -> Just $ Fixed y
      ys  -> Just $ Possible ys
    pruneCell x = Just x

-- And apply that to whole grid
pruneGrid' :: Grid -> Maybe Grid
pruneGrid' grid =
    traverse pruneCells grid
    >>= fmap transpose . traverse pruneCells . transpose

pruneGrid :: Grid -> Maybe Grid
pruneGrid = fixM pruneGrid'
  where
    fixM f x = f x >>= \x' -> if x' == x then return x else fixM f x'

{- Solver step
  We assume one of the possible values in possible list and make it fixed
  Cell with smallest amount of possibilities is chosen
  We have 2 cases:
  1. Possible list has 2 possibilities => return two grids with fixed numbers in chosen cell
  2. > 2 possibilities => return one fixed and one non-fixed cell
-}
nextGrids :: Int -> Grid -> Maybe (Grid, Grid)
nextGrids problemSize grid = do
  (i, first@(Fixed _), rest) <-
        fixCell
        . minimumBy (compare `on` (possibilityCount . snd))
        . filter (isPossible . snd)
        . zip [0..]
        . concat
        $ grid
  pure (replace2D i first grid, replace2D i rest grid)
  where
    isPossible (Possible _) = True
    isPossible _            = False

    possibilityCount (Possible xs) = length xs
    possibilityCount (Fixed _)     = 1

    fixCell (i, Possible [x, y]) = Just (i, Fixed x, Fixed y)
    fixCell (i, Possible (x:xs)) = Just (i, Fixed x, Possible xs)
    fixCell _                    = Nothing

    replace2D :: Int -> a -> [[a]] -> [[a]]
    replace2D i v =
      let (x, y) = (i `quot` problemSize, i `mod` problemSize) in replace x (replace y (const v))
    replace p f xs = [if i == p then f x else x | (x, i) <- zip xs [0..]]

{- In order to solve puzzle, after applying views we use backtracking algorithm.
  Traverse through the tree of possible grids leading to 1 proper solution.
  Check each step - If grid is incorrect: fixed duplicates or no possibilities - cut the branch.
-}
solve :: Int -> Grid -> Maybe Grid
solve problemSize grid = pruneGrid grid >>= solve' problemSize
  where
    solve' ps g
      | isGridInvalid g = Nothing
      | isGridFilled g  = Just g
      | otherwise       =
          nextGrids ps g >>= (\(grid1, grid2) -> solve ps grid1 <|> solve ps grid2)

isGridFilled :: Grid -> Bool
isGridFilled = all isFixed . concat
  where
    isFixed (Fixed _) = True
    isFixed _         = False

isGridInvalid :: Grid -> Bool
isGridInvalid grid =
  any isInvalidRow grid
  || any isInvalidRow (transpose grid)
  where
    isInvalidRow row =
      let fixeds         = [x | Fixed x <- row]
          emptyPossibles = [x | Possible x <- row, null x]
      in hasDups fixeds || not (null emptyPossibles)

    hasDups l = hasDups' l []

    hasDups' [] _ = False
    hasDups' (y:ys) xs
      | y `elem` xs = True
      | otherwise   = hasDups' ys (y:xs)

runCase :: Int -> [Int] -> [Int] -> [Int] -> [Int] -> Maybe Grid
runCase size left right up bottom =
  let
    grid = generateGrid size
    applyLeft = applyLeftView size left grid
    applyRight = applyRightView size right applyLeft
    applyUp = applyUpperView size up applyRight
    applyBottom = applyBottomView size bottom applyUp
    pruned = traverse pruneCells applyBottom
    grid' = pruned >>= fmap transpose . traverse pruneCells . transpose
    solution = grid' >>= solve size
  in solution

-- given example
testCase1 = runCase 4 [0,0,4,0] [0,3,0,0] [3,0,1,0] [0,0,0,0]

main :: IO ()
main = do
  print "Enter problem size"
  problemSize <- readInt
  let possibleGrid = generateGrid problemSize
  print "Enter upper views"
  upperViewsLine <- getLine
  let upperViews = readViews upperViewsLine
  print "Enter left views"
  leftViewsLine <- getLine
  let leftViews = readViews leftViewsLine
  print "Enter right views"
  rightViewsLine <- getLine
  let rightViews = readViews rightViewsLine
  print "Enter bottom views"
  bottomViewsLine <- getLine
  let bottomViews = readViews bottomViewsLine

  let solution = runCase problemSize leftViews rightViews upperViews bottomViews
  case solution of
      Just a  -> putStrLn (showGrid a)
      Nothing -> print "Program failed"
