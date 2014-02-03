{-
A solver for a Regular Expression Crossword

See: http://almostobsolete.net/regex-crossword/part1.html

Feb 2014
Thomas Parslow
tom@almostobsolete.net
-}
import Regex as Regex

import Data.List
import Data.Function
import qualified Data.Map as Map
import qualified Data.Set as Set

-- We only store the X and Y coords, we generate Z on demand
type Coords = (Int, Int)
type Possibilities = Set.Set Char
type GameState = Map.Map Coords Possibilities

-- A set of all possible letters that any hexagon could be (the puzzle
-- only has capital letters)
allLetters :: Possibilities
allLetters = Set.fromList ['A'..'Z']

-- Are the given set of X, Y coordinates within the puzzle bounding
-- hexagon?
validCoords :: Int -> Int -> Bool
validCoords x y = ok x && ok y && ok z
    where z = -(x + y)
          ok i = abs i <= 6

-- The starting Gamestate in which we know nothing about any of the
-- hexagons (so they all have all the letters as their possibilities)
starting :: GameState
starting = Map.fromList [((x,y), allLetters) |
                         x <- [-6..6],
                         y <- [-6..6],
                         validCoords x y]
                                                   
-- Output the Gamestate as ASCII for debugging. Is parametrised with a
-- cell-printing function to allow different debug outputs to be
-- constructed easily
showGameState :: GameState -> (Int -> Int -> Int -> [Char] -> [Char]) -> String
showGameState gamestate showCell = intercalate "\n" rows
    where rows = map showRow [-6..6]
          showRow x = (replicate (abs x) ' ') ++ (concatMap (showCell' x) [-6..6])
          showCell' x y =
              let z = -(x+y) in
              case Map.lookup (x, y) gamestate of
                Just c -> showCell x y z (Set.toList c) ++ " "
                Nothing -> ""
                           
-- A cell printing function for use with showGameState. Displays the
-- letter if the Hexagon has been solved otherwise displays a . or a *
-- depending on if the possibilities have been narrowed down at all or
-- not.
cellSolvedState :: Int -> Int -> Int -> [Char] -> String
cellSolvedState x y z chars =
    case chars of
      [] -> "!"
      char@[_] -> char
      _ -> if length chars == 26 then
               "."
           else
               "*"
           
-- The list of coordinates that each regex must match against
regexCoordinates :: [[Coords]]
regexCoordinates  = xside ++ yside ++ zside
    where xside = [[(x,y) | y <- [-6..6], validCoords x y] | x <- [-6..6]]
          yside = [[(x,y) | z <- [-6..6], let x = -(y + z), validCoords x y] | y <- [-6..6]]
          zside = [[(x,y) | x <- [-6..6], let y = -(x + z), validCoords x y] | z <- [-6..6]]
                                                  

-- Read a list of keys from a Map, run them all through a function,
-- then write them backb
bulkAdjust :: Ord k => ([v] -> [v]) -> [k] -> Map.Map k v -> Map.Map k v
bulkAdjust fn ks m = foldr (uncurry Map.insert) m (zip ks (fn vs))
    where vs = map (m Map.!) ks

-- Run an iteration of the solver, take a set of regexs and a
-- GameState and returns an updated (narrowed) GameState
runIteration :: [Regex.Regex] -> GameState -> GameState
runIteration compiled gamestate = foldr update gamestate (zip regexCoordinates compiled) 
    where update (coords, re) gamestate = bulkAdjust (match re) coords gamestate

loadRegexs filename = do
  fileContents <- readFile filename
  let regexs = filter (/="") $ lines fileContents
  return $ map Regex.compile regexs

run compiledRegexs gamestate i = do
  -- Print the current state of the game
  putStrLn ""
  putStrLn $ "Iteration " ++ (show i)
  putStrLn $ showGameState gamestate cellSolvedState      
           
  -- Run an iteration
  let gamestate' = runIteration compiledRegexs gamestate

  -- Check if we've terminated (if the new gamestate is the
  -- same as the old one)
  if gamestate == gamestate' then
      do
        putStrLn ""
        putStrLn "Done!"
        return ()
  else
      run compiledRegexs gamestate' (i+1)
                                   
main = do
  compiledRegexs <- loadRegexs "regexs.txt"
  run compiledRegexs starting 0
