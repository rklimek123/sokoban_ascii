{-# LANGUAGE OverloadedStrings #-}
import Data.Char
import System.IO

{- List Extensions -}
foldList :: (a -> b -> b) -> b -> [a] -> b
foldList _ acc [] = acc
foldList func acc (lh:lt) = foldList func (func lh acc) lt

elemList :: Eq a => a -> [a] -> Bool
elemList el list =
    foldList (\toComp res -> res || el == toComp) False list

reverseList :: [a] -> [a]
reverseList l =
    foldList (:) [] l

appendList :: [a] -> [a] -> [a]
appendList l1 l2 =
    foldList (:) l2 $ reverseList l1

listLength :: [a] -> Integer
listLength l =
    foldList (\_ acc -> acc + 1) 0 l

filterList :: (a -> Bool) -> [a] -> [a]
filterList pred l =
    reverseList $ foldList (\el acc ->
        if pred el then el:acc else acc) [] l

data Pair a b = Pair a b

pairFirst :: Pair a b -> a
pairFirst (Pair a b) = a

pairSecond :: Pair a b -> b
pairSecond (Pair a b) = b

unpackMaybe :: Maybe a -> a
unpackMaybe (Just a) = a

nth :: [a] -> Integer -> a
nth l n =
  (unpackMaybe.pairSecond) $ foldList
        (\el (Pair cnt res) ->
            if cnt == 0 then (Pair (cnt - 1) (Just el)) else (Pair (cnt - 1) res))
        (Pair n Nothing) l

mapList :: (a -> b) -> [a] -> [b]
mapList mapping l =
    reverseList $ foldList (\el acc -> (mapping el):acc) [] l

andList :: [Bool] -> Bool
andList l = foldList (&&) True l

allList :: (a -> Bool) -> [a] -> Bool
allList pred = andList . (mapList pred)

{- Graph logic -}

dfsIfOk :: Eq a => a -> (a -> [a]) -> (a -> Bool) -> [a]
dfsIfOk initialNode neighbours isOk =
    propInner initialNode [initialNode]
    where
        propInner currentNode visited =
            if isOk currentNode then
                foldList(\node acc ->
                    let visited' = appendList acc visited in
                    if elemList node visited'
                        then acc
                        else node:
                            (appendList acc
                                (propInner node (node:visited'))
                            )) [] (neighbours currentNode)
            else []

isGraphClosed :: Eq a => a -> (a -> [a]) -> (a -> Bool) -> Bool
isGraphClosed initial neighbours isOk =
    allList isOk (initial:(dfsIfOk initial neighbours isOk))

reachable :: Eq a => a -> a -> (a -> [a]) -> Bool
reachable v initial neighbours =
    propInner [initial] [initial]
    where
        propInner [] visited = False
        propInner (n:l) visited =
            let visited' = n:visited in
            if n == v
                then True
            else propInner
                (foldList
                    (\neigh acc -> if elemList neigh visited' then acc else neigh:acc)
                    l
                    (neighbours n))
                visited'

allReachable :: Eq a => [a] -> a -> (a -> [a]) -> Bool
allReachable vs initial neighbours =
    andList $ mapList (\v -> reachable v initial neighbours) vs


{- Activity -}
data Activity world = Activity {
    actState  :: world,
    actHandle :: (Event -> world -> world),
    actDraw   :: (world -> Screen)
}
    
data Event = KeyPress String
type Screen = String

screenWidth = 71
screenHeight = 23
  
resettable :: Activity s -> Activity s
resettable (Activity state0 handle draw) =
  Activity state0 handle' draw
  where 
        handle' (KeyPress key) _ | key == "ESC" = state0
        handle' e s = handle e s

data MetaState world = StartScreen | Running world deriving Eq

withMenuScreen :: (s -> Bool) -> Activity s -> Activity (MetaState s)
withMenuScreen isEnd (Activity state0 handle draw)
  = Activity state0' handle' draw'
  where
    state0' = StartScreen

    handle' (KeyPress key) StartScreen
         | key == " "                  = Running state0
    handle' _              StartScreen = StartScreen

    handle' e             (Running st) = Running (handle e st)

    draw' StartScreen = renderPicture startScreen
    draw' (Running s) = draw s


data WithUndo a = WithUndo a [a]

withUndo :: Eq a => Activity a -> Activity (WithUndo a)
withUndo (Activity state0 handle draw) = Activity state0' handle' draw' where
    state0' = WithUndo state0 []
    handle' (KeyPress key) (WithUndo s stack) | key == "U"
      = case stack of s':stack' -> WithUndo s' stack'
                      []        -> WithUndo s []
    handle' e              (WithUndo s stack)
       | s' == s = WithUndo s stack
       | otherwise = WithUndo (handle e s) (s:stack)
      where s' = handle e s
    draw' (WithUndo s _) = draw s


cleanScreen :: IO()
cleanScreen = putStr "\ESCc"

runActivity :: Activity s -> IO()
runActivity (Activity state handle draw) =
    do
        hSetBuffering stdin NoBuffering
        cleanScreen
        putStrLn $ draw state
        x <- getContents
        go x state

    where
        go stream currentState =
            do
                converted <- convertAnsi stream
                cleanScreen
                putStr $ draw (newStateFromPair converted currentState)
                go (pairSecond converted) (newStateFromPair converted currentState)

        newStateFromPair pair curSt =
          handle (KeyPress (toUpperStr $ pairFirst pair)) curSt

        toUpperStr :: String -> String
        toUpperStr s =
            foldr
                (\el acc -> (toUpper el):acc)
                [] s

        convertAnsi :: String -> IO (Pair String String)
        convertAnsi ('\ESC':t1) =
          case t1 of
              ('[':t2) ->
                  case t2 of
                      ('A':t3) -> return $ Pair "Up" t3
                      ('B':t3) -> return $ Pair "Down" t3
                      ('C':t3) -> return $ Pair "Right" t3
                      ('D':t3) -> return $ Pair "Left" t3
                      _ -> return $ Pair "" t2
              ('\ESC':t2) -> return $ Pair "Esc" t2
              _ -> return $ Pair "" t1
        convertAnsi (h:t) = return $ Pair [h] t
        convertAnsi [] = return $ Pair "" ""


{-/ Codeworld API \-}
type DrawFun = Integer -> Integer -> Char
type Picture = DrawFun -> DrawFun
blank = id
(&) = (.)

lettering :: String -> (DrawFun -> DrawFun)
lettering s d =
  (\x y ->
    if y == 0 then
      if even n then
        if x <= base && x > (-base) then
          nth s (x + base - 1)
        else d x y
      else
        if x <= base && x >= (-base) then
          nth s (x + base)
        else d x y
    else
      d x y)

  where
    n = listLength s
    base = n `div` 2

translated :: Integer -> Integer -> Picture -> (DrawFun -> DrawFun)
translated x y pic =
  (\d x2 y2 -> pic d (x2 - x) (y2 + y))
  & (\d x2 y2 -> d (x2 + x) (y2 - y))
{-\ Codeworld API /-}

{- View -}
renderPicture :: Picture -> Screen
renderPicture pictureTransform =
  useDrawFunction pic
  where
    pic :: DrawFun
    pic = pictureTransform (\x y -> ' ')

    useDrawFunction :: DrawFun -> Screen
    useDrawFunction d =
      foldr (\y acc -> drawLine y acc) "" [minY..maxY]
      where
        minY = -screenHeight `div` 2
        maxY = screenHeight `div` 2

        minX = -screenWidth `div` 2
        maxX = screenWidth `div` 2

        drawLine y acc =
          foldr (\x accInner -> (d x y):accInner) ('\n':acc) [minX..maxX]


startScreenBase :: Picture
startScreenBase =
  translated 0 2    (lettering "███████  ██████  ██   ██  ██████  ██████   █████  ███    ██") &
  translated 0 1    (lettering "██      ██    ██ ██  ██  ██    ██ ██   ██ ██   ██ ████   ██") &
                     lettering "███████ ██    ██ █████   ██    ██ ██████  ███████ ██ ██  ██" &
  translated 0 (-1) (lettering "     ██ ██    ██ ██  ██  ██    ██ ██   ██ ██   ██ ██  ██ ██") &
  translated 0 (-2) (lettering "███████  ██████  ██   ██  ██████  ██████  ██   ██ ██   ████")


endScreen :: Integer -> Bool -> Picture
endScreen moveCount hasNextLvl =
    lettering ("Level passed in " ++ show moveCount ++ " moves!") &
    if hasNextLvl
        then
            translated 0 (-2) (lettering "[N] - Next level")
        else
            blank

{-/ Tiles \-}
charPicture :: Char -> (DrawFun -> DrawFun)
charPicture c d =
  (\x y -> if x == 0 && y == 0 then c else d x y)

wall :: Picture
wall = charPicture '#'

player :: Picture
player = charPicture '@'

playerOnStorage :: Picture
playerOnStorage = charPicture '+'

box :: Picture
box = charPicture '$'

boxOnStorage :: Picture
boxOnStorage = charPicture '*'

storage :: Picture
storage = charPicture '.'

ground :: Picture
ground = charPicture ' '
{-\ Tiles /-}


{- Model -}
data Tile = Wall | Ground | Storage | Box | Blank deriving Eq

drawTile :: Tile -> Picture
drawTile Wall = wall
drawTile Ground = ground
drawTile Storage = storage
drawTile Box = box
drawTile Blank = blank

drawTileAt :: Tile -> Coord -> Picture
drawTileAt tile (C x y) =
  translated x y (drawTile tile)


data Coord = C {
  cx :: Integer,
  cy :: Integer
} deriving Eq

adjacentCoord :: Direction -> Coord -> Coord
adjacentCoord U (C x y) = C x (y + 1)
adjacentCoord R (C x y) = C (x + 1) y
adjacentCoord D (C x y) = C x (y - 1)
adjacentCoord L (C x y) = C (x - 1) y


removeBoxes :: Mapping -> Mapping
removeBoxes maze =
    f . maze
      where
        f t
          | Box == t = Ground
          | otherwise = t


data Direction = U | R | D | L deriving Eq

type Mapping = Coord -> Tile

data State = S {
  stPlayer   :: Coord,
  stDir      :: Direction,
  stBoxes    :: [Coord],
  stStartMap :: Mapping,
  stMoves    :: Integer,
  stCurrentLvl :: Integer,
  stMazes    :: [Maze]
}

{- Not true equality, doesn't compare mappings -}
instance Eq State where
  S p1 d1 b1 _ m1 cl1 _ == S p2 d2 b2 _ m2 cl2 _ =
    p1 == p2 && d1 == d2 && b1 == b2 && m1 == m2 && cl1 == cl2


drawState :: State -> Screen
drawState s@(S playerCoord@(C px py) dir boxes startMap moves currentLvl mazes) =
    renderPicture pic

    where
      playerTexture =
        if playerIsOnStorage then playerOnStorage
        else player

      playerIsOnStorage =
        startMap playerCoord == Storage

      drawBoxes :: Mapping -> Coord -> Picture -> Picture
      drawBoxes mapping b@(C x y) acc =
        acc &
          if mapping b == Storage then
            translated x y boxOnStorage
          else
            drawTileAt Box b

      pic =
        if isWinning s then endScreen moves ((listLength mazes) - 1 /= currentLvl)
        else
            translated 30 10 (lettering (show moves)) &
            translated (-30) (-10) (lettering ("Level " ++ (show (currentLvl + 1)))) &
            translated px py playerTexture &
            foldList (drawBoxes startMap) blank boxes &
            foldList
                (\c acc ->
                acc &
                    drawTileAt (startMap c) c
                ) blank (mazeCoordsToDraw (Maze (C px py) startMap))
    

boxCoords (Maze initial startMap) =
  foldList
    (\c acc -> if Box == startMap c then c:acc else acc)
    []
    (mazeCoordsToDraw (Maze initial startMap))
    

isWinning :: State -> Bool
isWinning s@(S player _ boxes startMap _ _ _) =
    allList (\c -> not (reachable c player graph) || startMap c == Storage) boxes
    where
        graph = getMappingGraph startMap


{- Maze -}
data Maze = Maze Coord Mapping

getMazeMapping :: Maze -> Mapping
getMazeMapping (Maze _ mapping) = mapping

mazeToState :: Maze -> State
mazeToState m@(Maze initial mapping) =
    S initial D initialBoxes (removeBoxes mapping) 0 0 []
    where
        initialBoxes = filterList (\c -> reachable c initial (getMazeGraph m)) (boxCoords m)

getMappingGraph :: Mapping -> (Coord -> [Coord])
getMappingGraph mapping (C x y) =
    filterList (\c -> mapping c /= Wall) [(C (x-1) y), (C (x+1) y), (C x (y-1)), (C x (y+1))]

getMappingGraphToDraw :: Mapping -> (Coord -> [Coord])
getMappingGraphToDraw mapping (C x y) =
    filterList (\c -> mapping c /= Blank) [(C (x-1) y), (C (x+1) y), (C x (y-1)), (C x (y+1))]

mazeCoordsToDraw :: Maze -> [Coord]
mazeCoordsToDraw (Maze initial startMap) =
    initial:(dfsIfOk initial (getMappingGraphToDraw startMap) (\c -> True))

getMazeGraph :: Maze -> (Coord -> [Coord])
getMazeGraph (Maze _ mapping) = getMappingGraph mapping


isClosed :: Maze -> Bool
isClosed m@(Maze starting mapping) =
    (mapping starting == Ground || mapping starting == Storage) &&
        isGraphClosed starting (getMazeGraph m) (\c -> mapping c /= Blank)
        

isSane :: Maze -> Bool
isSane m@(Maze starting mapping) =
    reachableStoragesCount >= reachableBoxesCount
    where
        reachableFields = dfsIfOk starting (getMazeGraph m) (\c -> mapping c /= Blank)
        reachableStoragesCount =
            listLength $ filterList (\c -> mapping c == Storage) reachableFields
        reachableBoxesCount =
            listLength $ filterList (\c -> mapping c == Box) reachableFields



{- Event controller -}
coordIsBox :: State -> Coord -> Bool
coordIsBox (S _ _ boxes _ _ _ _) c = elemList c boxes

coordIsWall :: State -> Coord -> Bool
coordIsWall (S _ _ _ startMap _ _ _) c = Wall == startMap c

coordIsBlocking :: State -> Coord -> Bool
coordIsBlocking s c = coordIsBox s c || coordIsWall s c

keyInput :: Event -> State -> State
keyInput (KeyPress key) s@(S pl _ _ _ moves currentLvl mazesList)
    | key == "RIGHT" = nextCoord R
    | key == "UP"    = nextCoord U
    | key == "LEFT"  = nextCoord L
    | key == "DOWN"  = nextCoord D
    | key == "N"     = nextLevel
  where
    nextLevel =
        if (listLength mazesList) - 1 > currentLvl
            then (mazeToState (nth mazesList (currentLvl + 1))){stCurrentLvl = currentLvl + 1, stMazes = mazesList}
            else s
    nextCoord dir
        | coordIsWall nextS adj = nextS
        | coordIsBox nextS adj =
            if coordIsBlocking nextS (adjacentCoord dir adj) then nextS
            else
              nextS{
                stPlayer = adj,
                stBoxes = map (\b -> if b == adj then adjacentCoord dir adj else b) (getStateBoxes nextS)}
        | otherwise = nextS{stPlayer = adj}
      where
        adj = adjacentCoord dir pl
        nextS = s{stDir = dir, stMoves = moves + 1}
        getStateBoxes (S _ _ bxs _ _ _ _) = bxs
keyInput _ s      = s

{- Level initialization -}
{-/ Mazes \-}

maze1 :: Maze
maze1 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 4  || abs y > 4  = Blank
      | abs x == 4 || abs y == 4 = Wall
      | x ==  2 && y <= 0        = Wall
      | x ==  3 && y <= 0        = Storage
      | x >= -2 && y == 0        = Box
      | otherwise                = Ground

maze2 :: Maze
maze2 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 6  || abs y > 6  = Blank
      | abs x == 6 || abs y == 6 = Wall
      | x == 5                   = Storage
      | x == 4                   = Box
      | otherwise                = Ground

maze3 :: Maze
maze3 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 4  || abs y > 4  = Blank
      | abs x == 4 || abs y == 4 = Wall
      | x ==  2 && y <= 0        = Storage
      | x ==  3 && y <= 0        = Storage
      | x >= -2 && y == 0        = Box
      | x >= -2 && y == (-2)     = Box
      | otherwise                = Ground

mazes :: [Maze]
mazes = [maze1, maze2, maze3]

-- Brak większości ścian. Gracz w więzieniu
badMaze1 :: Maze
badMaze1 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 4  || abs y > 4  = Blank  -- blank
      | x == (-1) && abs (y - 1) <= 1 = Wall
      | x == 1 && abs (y - 1) <= 1 = Wall
      | y == 2 && abs x <= 1 = Wall
      | y == 0 && abs x <= 1 = Wall
      | x ==  2 && y <= 0        = Wall  -- wall
      | x ==  3 && y <= 0        = Storage  -- storage
      | x >= -2 && y == 0        = Box  -- box
      | otherwise                = Ground  -- ground

-- Za dużo boxów.
badMaze2 :: Maze
badMaze2 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 4  || abs y > 4  = Blank  -- blank
      | abs x == 4 || abs y == 4 = Wall  -- wall
      | x ==  3 && y <= 0        = Storage  -- storage
      | x >= -2 && y == 0        = Box  -- box
      | otherwise                = Ground  -- ground

-- Za dużo boxów.
badMaze3 :: Maze
badMaze3 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 4  || abs y > 4  = Blank  -- blank
      | abs x == 4 || abs y == 4 = Wall  -- wall
      | x ==  2 && y <= 0        = Wall  -- wall
      | x ==  3 && y <= (-1)     = Storage  -- storage
      | x >= -2 && y == 0        = Box  -- box
      | otherwise                = Ground  -- ground

-- Brak większości ścian.
badMaze4 :: Maze
badMaze4 = Maze start mapping where
    start = (C 0 1)
    mapping (C x y)
      | abs x > 4  || abs y > 4  = Blank  -- blank
      | x ==  2 && y <= 0        = Wall  -- wall
      | x ==  3 && y <= 0        = Storage  -- storage
      | x >= -2 && y == 0        = Box  -- box
      | otherwise                = Ground  -- ground

badMazes :: [Maze]
badMazes = [badMaze1, badMaze2, badMaze3, badMaze4]
{-\ Mazes /-}

{-/ Mazes info \-}
pictureOfBools :: [Bool] -> Picture
pictureOfBools xs = translated ((-n) `div` 2) 0 (go 0 xs)
  where n = listLength xs
        k = findK 0 -- k is the integer square of n
        findK i | i * i >= n = i
                | otherwise  = findK (i+1)
        go _ [] = blank
        go i (b:bs) =
          translated i 0 (pictureOfBool b)
          & go (i+1) bs

        pictureOfBool True =  lettering "o"
        pictureOfBool False = lettering "x"

etap4 =
    translated 0 6 startScreenBase &
    translated (-20) 0 (lettering "Good closed levels") &
    translated (-20) (-1) (pictureOfBools (mapList isClosed mazes)) &
    translated 20 (-3) (lettering "Bad closed levels") &
    translated 20 (-4) (pictureOfBools (mapList isClosed badMazes)) &
    translated (-20) (-6) (lettering "Good sane levels") &
    translated (-20) (-7) (pictureOfBools (mapList isSane mazes)) &
    translated 20 (-9) (lettering "Bad sane levels") &
    translated 20 (-10) (pictureOfBools (mapList isSane badMazes))

startScreen = etap4

{-\ Mazes info /-}

startState = (mazeToState (nth mazes 0)){stCurrentLvl = 0, stMazes = mazes}

etap5 :: IO()
etap5 = (runActivity.withUndo.(withMenuScreen isWinning).resettable) (Activity startState keyInput drawState)

main :: IO()
main = etap5

{- Extras -}
addBoxes :: [Coord] -> Mapping -> Mapping
addBoxes boxes maze coord
    | elemList coord boxes = Box
    | otherwise = maze coord