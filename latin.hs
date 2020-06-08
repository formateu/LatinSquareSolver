import Data.Char
import Data.List
import Data.Function

data Cell = Fixed Int | Possible [Int] deriving (Show, Eq)
type Row  = [Cell]
type Grid = [Row]

showGrid :: Grid -> String
showGrid = unlines . map (unwords . map showCell)
  where
    showCell (Fixed x) = show x
    showCell _ = "."

showGridWithPossibilities :: Grid -> String
showGridWithPossibilities = unlines . map (unwords . map showCell)
  where
    showCell (Fixed x)     = show x ++ "  "
    showCell (Possible xs) =
      (++ "]")
      . Data.List.foldl' (\acc x -> acc ++ if x `elem` xs then show x else " ") "["
      $ [1..4]

generateCell :: Int -> Cell
generateCell size = Possible [1..size]

generateRow :: Int -> Row
generateRow size = generateInternal size size
    where generateInternal 0 _ = []
          generateInternal currPos n = (generateCell size):(generateInternal (currPos-1) n)

generateGrid :: Int -> Grid
generateGrid size = generateInternal size size
    where generateInternal 0 _ = []
          generateInternal currPos n = (generateRow size):(generateInternal (currPos-1) n)

readViews :: String -> [Int]
readViews s = fmap readCell s
    where readCell '.' = 0
          readCell c = Data.Char.digitToInt $ c

readInt :: IO Int
readInt = do
    int <- getLine
    return (read int)

removeFromList :: Eq a => a -> [a] -> [a]
removeFromList _ []                 = []
removeFromList x (y:ys) | x == y    = removeFromList x ys
                    | otherwise = y : removeFromList x ys

removeFrom :: Int -> Cell -> Cell
removeFrom toRemove (Fixed value)
    | value == toRemove = Possible []

removeFrom toRemove (Possible intList) = Possible (removeFromList toRemove intList)

removeIncremental :: Int -> Int -> Row -> Row
removeIncremental howManyWeSee problemSize row = removeGEGrowing (problemSize-howManyWeSee+2) problemSize row

removeGEGrowing :: Int -> Int -> Row -> Row
removeGEGrowing h p (x:xs)
    | h <= p =  (removeGE h x):(removeGEGrowing (h+1) p xs)
    | otherwise = x:xs

removeGEGrowing _ _ [] = []

removeGE :: Int -> Cell -> Cell
removeGE toRemove (Possible list) = Possible (removeGEInt toRemove list)

removeGE toRemove (Fixed n)
    | n == toRemove = Possible []
    | otherwise = Fixed n

removeGEInt :: Int -> [Int] -> [Int]
removeGEInt toRemove (l:ls)
    | l < toRemove = l:(removeGEInt toRemove ls)
    | otherwise = []

applyViewImpl :: Int -> Int -> Row -> Row
applyViewImpl problemSize howManyWeSee (xs:ys)
    | howManyWeSee == 0 = (xs:ys)
    | howManyWeSee == problemSize = fmap Fixed [1..problemSize]
    | howManyWeSee == 1 = (Fixed problemSize):ys
    | howManyWeSee == 2 = (removeFrom problemSize xs):ys
    | otherwise = removeIncremental howManyWeSee problemSize (xs:ys)

applyView :: Int -> [Int] -> (Grid -> Grid) -> Grid -> Grid
applyView problemSize upperView transformFunc grid = transformFunc (map (\(a,b) -> applyViewImpl problemSize a b) $ zip upperView $ transformFunc grid)

applyUpperView :: Int -> [Int] -> Grid -> Grid
applyUpperView problemSize upperView grid = applyView problemSize upperView transpose grid

applyLeftView :: Int -> [Int] -> Grid -> Grid
applyLeftView problemSize leftView grid =  applyView problemSize leftView id grid

applyRightView :: Int -> [Int] -> Grid -> Grid
applyRightView problemSize rightView grid = applyView problemSize rightView (transpose . reverse . transpose) grid

applyBottomView :: Int -> [Int] -> Grid -> Grid
-- applyBottomView problemSize bottomView grid = applyView problemSize bottomView (reverse . transpose) grid
applyBottomView problemSize bottomView grid = transpose $ reverse (map (\(a,b) -> applyViewImpl problemSize a b) $ zip bottomView $ reverse $ transpose grid)

pruneCells :: [Cell] -> Maybe [Cell]
pruneCells cells = traverse pruneCell cells
  where
    fixeds = [x | Fixed x <- cells]

    pruneCell (Possible xs) = case xs Data.List.\\ fixeds of
      []  -> Nothing
      [y] -> Just $ Fixed y
      ys  -> Just $ Possible ys
    pruneCell x = Just x

-- test
grid = generateGrid 4
applyLeft = applyLeftView 4 [0,0,4,0] grid
applyRight = applyRightView 4 [0,3,0,0] grid
applyUp = applyUpperView 4 [3,0,1,0] grid
applyBottom = applyBottomView 4 [0, 0, 0, 0] grid
Just pruned = traverse pruneCells applyLeft
Just grid' = fmap transpose . traverse pruneCells . transpose $ pruned

pruneGrid' :: Grid -> Maybe Grid
pruneGrid' grid =
    traverse pruneCells grid
    >>= fmap transpose . traverse pruneCells . transpose

pruneGrid :: Grid -> Maybe Grid
pruneGrid = fixM pruneGrid'
  where
    fixM f x = f x >>= \x' -> if x' == x then return x else fixM f x'

nextGrids :: Int -> Grid -> (Grid, Grid)
nextGrids problemSize grid =
  let (i, first@(Fixed _), rest) =
        fixCell
        . Data.List.minimumBy (compare `Data.Function.on` (possibilityCount . snd))
        . filter (isPossible . snd)
        . zip [0..]
        . concat
        $ grid
  in (replace2D i first grid, replace2D i rest grid)
  where
    isPossible (Possible _) = True
    isPossible _            = False

    possibilityCount (Possible xs) = length xs
    possibilityCount (Fixed _)     = 1

    fixCell (i, Possible [x, y]) = (i, Fixed x, Fixed y)
    fixCell (i, Possible (x:xs)) = (i, Fixed x, Possible xs)
    fixCell _                    = error "Impossible case"

    replace2D :: Int -> a -> [[a]] -> [[a]]
    replace2D i v =
      let (x, y) = (i `quot` problemSize, i `mod` problemSize) in replace x (replace y (const v))
    replace p f xs = [if i == p then f x else x | (x, i) <- zip xs [0..]]

isGridFilled :: Grid -> Bool
isGridFilled grid = null [ () | Possible _ <- concat grid ]

isGridInvalid :: Grid -> Bool
isGridInvalid grid =
  any isInvalidRow grid
  || any isInvalidRow (Data.List.transpose grid)
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

solve :: Int -> Grid -> Maybe Grid
solve problemSize grid = pruneGrid grid >>= (solve' problemSize)
  where
    solve' ps g
      | isGridInvalid g = Nothing
      | isGridFilled g  = Just g
      | otherwise       =
          let (grid1, grid2) = nextGrids ps g
          in (solve ps grid1) <|> (solve ps grid2)

main :: IO ()
main = do print "Enter problem size"
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
          let afterLeft = applyLeftView problemSize leftViews possibleGrid
          let afterRight = applyRightView problemSize rightViews afterLeft
          let afterUp = applyUpperView problemSize upperViews afterRight
          let afterBot = applyBottomView problemSize bottomViews afterUp
          case pruneGrid afterBot of
              Just a -> putStrLn $ showGridWithPossibilities a
              Nothing -> print "Program failed"