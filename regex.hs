{-

A VM based regular expression engine that narrows down a set of
possible values for each position in its input.

Probably has some bugs but it works well enough for its purpose (to
solve the regex crossword)

Supports:

 - Literal Characters: A, B, C (capital letters only as that's all
   that was needed for the puzzle)
 - Character classes: [AZY], [^ABC] 
 - Wildcards: .
 - Bracketed sub-expressions: (ABCD)
 - Maybe match: A?, (XYZ)?
 - Match zero or more: B*, [ZYS]*
 - Match one or more: B+, [ZYS]+
 - Mulitple Choices: ABC|DEF, (FOO|BAR)
 - Back references: (ABD)(XYZ)\2\1

Feb 2014
Thomas Parslow
tom@almostobsolete.net
-}
module Regex (compile, match, Regex) where

import Data.Array
import Data.Maybe
import Data.Char
import System.IO.Unsafe
import qualified Data.Set as Set
import qualified Data.Map as Map

-- A instruction for the VM
data Instruction =   MatchChars (Set.Set Char)
                 | Split Int Int
                 | End
                 | StartGroup Int
                 | EndGroup Int
                 | BackRef Int
                   deriving Show

-- A machine state has a set of threads, the state for each thread
-- consists of...
data ThreadState = ThreadState {
    -- ...the program counter, an index into the instructions array
    pc :: Int,
    -- The set of characters that could match for each of the
    -- postions already considered (in reverse order)
    matches :: [Set.Set Char],
    -- A list of start indexes and end indexes for groups in the
    -- input plus a list of locations of backrefs to groups
    groups :: (Map.Map Int Int, Map.Map Int Int, Map.Map Int [Int]),
    -- Number of chars to match before the backref is exhausted
    -- (always 0 if we're not mid-backref)
    backrefCountdown :: Int
  } deriving (Show, Ord, Eq)

-- Current state of the regex VM, including the programm (a list of
-- instructions) the set of current running threads and the remaining
-- unconsumed input
data MachineState = MachineState {
    -- We use an array instead of a list for the instructions in the
    -- machine state so that we can access a given numbered
    -- instruction quickly
    instructions :: (Array Int Instruction),
    threads :: Set.Set ThreadState,
    inputTail :: [Set.Set Char]
  } deriving Show

-- A compiled regular expression is just a list of instructions
type Regex = [Instruction]

    
------------
-- The VM --
------------


-- Part of the public interface to the module, takes a compiled regex
-- (a list of Instruction items) and a list of sets giving the
-- possibile characters at each location, returns a newly narrowed
-- down list of sets.
match :: Regex -> [Set.Set Char] -> [Set.Set Char]
match instructions input = getMatches $ run $ mkMachineState instructions input


-- Create a machine state from a list of 
mkMachineState :: Regex -> [Set.Set Char] -> MachineState
mkMachineState instructions input =
  MachineState instructionsArray threadSet input
      where instructionsArray = listArray (0,length instructions - 1) instructions
            threadSet = Set.fromList [ThreadState 0 [] (Map.empty, Map.empty, Map.empty) 0]

-- Set the virtual machine through one location of the input
step :: MachineState -> MachineState
step (MachineState instructions threads (x:xs)) = MachineState instructions (Set.fromList threads') xs
  where threads' = concatMap (runThread instructions x) (Set.toList threads)

-- Repeatedly step over the whoe of the input
run ms@(MachineState _ _ (_:_)) = run . step $ ms
run ms = ms

-- Run through any split commands and produce 0 or more threads ready to consume an input
splitThread :: (Array Int Instruction) -> ThreadState -> [ThreadState]
splitThread instructions ts@(ThreadState pc ms groups@(startIndexes, endIndexes, backRefs) bc) = exec (instructions ! pc)
  where exec (MatchChars s) = [ts]
        exec (BackRef g) = [ts]
        -- For split we split execution into 2 threads and run those threads to consume the input
        exec (Split a b) = st (ThreadState (pc+a) ms groups bc) ++ st (ThreadState (pc+b) ms groups bc)
        exec (StartGroup g) = st (ThreadState (pc+1) ms ((Map.insert g ((length ms)) startIndexes), endIndexes, backRefs) bc)
        exec (EndGroup g) = st (ThreadState (pc+1) ms (startIndexes, (Map.insert g (length ms) endIndexes), backRefs) bc)
        exec End = [ts]
        st = splitThread instructions 

-- Run the given thread forward enough to consume the next input (or
-- fail). Returns a list of threads (the one thread might split into
-- multiple threads or might fail and turn into no threads).
runThread :: Array Int Instruction -> Set.Set Char -> ThreadState -> [ThreadState]
runThread instructions x ts = let tss = splitThread instructions ts in
                            let notFailed = not . Set.null . head . matches in
                            filter notFailed $ concatMap (splitThread instructions) $ concatMap consume tss
  where consume (ThreadState pc ms groups bc) =
            case instructions ! pc of
              MatchChars s -> [ThreadState (pc+1) ((Set.intersection s x):ms) groups bc]
              BackRef g -> matchBackref instructions x (ThreadState pc ms groups bc) g
              -- TODO: Should use a Maybe here rather then relying on an empty set to trigger removal
              End -> [ThreadState pc (Set.empty:ms) groups bc]

-- Process a BakcRef instruction. This was the last bit added to the
-- code and it's pretty messy, should definitely be cleaned up but it
-- does work (at least well enough to solve the puzzle)
matchBackref instructions x (ThreadState pc ms groups@(startIndexes, endIndexes, backRefs) bc) group =
  if current >= end then
      runThread instructions x (ThreadState (pc+1) ms (startIndexes, endIndexes, insertInto ((length ms) - bc) group backRefs)  0)
  else
      let backrefIndexes = current:(Map.findWithDefault [] group backRefs) in
      let rms = reverse ms in
      let s = foldr Set.intersection x $ map (rms!!) backrefIndexes in
      let ms' = s:(reverse (foldr (replaceNth s) rms backrefIndexes)) in
      if current == end - 1 then
          [ThreadState (pc+1) ms' groups 0]
      else
          [ThreadState pc ms' groups (bc+1)]
  where insertInto value k map = Map.alter (Just . (value:) . (fromMaybe [])) k map
        start =  startIndexes Map.! group
        end = endIndexes Map.! group
        current = start + bc

-- Replace the nth value in a list with a new value
replaceNth value 0 (x:xs) = value:xs
replaceNth value index (x:xs) = x:replaceNth value (index-1) xs
replaceNth value 0 [] = []
replaceNth _ _ [] = error "Index out of range"

-- Take a completed machine and get the updated possible values  each position in the input
getMatches :: MachineState -> [Set.Set Char]
getMatches (MachineState instructions threads []) = reverse . combine $ map matches (filter isEnded (Set.toList threads))
  where isEnded (ThreadState pc _ _ _) = case (instructions ! pc) of
                                         End -> True
                                         otherwise -> False
        combine ([]:_) = []
        combine [] = []
        combine matches = let h = foldl Set.union Set.empty (map head matches) in
                          h : combine (map tail matches)

------------------
-- The compiler --
------------------

-- A manually written recursive decent parser, it's a bit messy and it
-- would be easier to use a library like Parsec but I fancied writing
-- one by hand. Doesn't produce an AST or anything and doesn't use a
-- lexxer, just transforms a String into a list of Instructions.


-- Part of the public interact to the module, take a regular
-- expression as a string and compile it to a list of instructions for
-- the VM
compile :: String -> Regex
compile xs = (numberGroups $ compile' xs) ++ [End]
  where compile' [] = [] 
        compile' xs = let (instr, rest) = compileOptions xs in
                      instr ++ compile' rest


-- All the letters that can be matched by the regex, we only care
-- about capitals for this problem
allLetters = Set.fromList ['A'..'Z']

-- We compile the groups with them all numbered 0 then add in the
-- numbers as a second step. Less state to pass around.
numberGroups :: Regex -> Regex
numberGroups instr = numberGroups' 0 [] instr
 where numberGroups' c open ((StartGroup _):xs) = (StartGroup c):numberGroups' (c+1) (c:open) xs
       numberGroups' c (closing:open) ((EndGroup _):xs) = (EndGroup closing):numberGroups' c open xs
       numberGroups' c _ ((EndGroup _):xs) = error "Mismatched brackets"
       numberGroups' c open (x:xs) = x:numberGroups' c open xs
       numberGroups' c [] [] = []
       numberGroups' c _ [] = error "Unclosed bracket"

-- Compile 1 or more options, if more than 1 then they'll be seperated
-- by | characters
compileOptions :: String -> (Regex, String)          
compileOptions xs = case read [] xs of
                      -- ([instr], rest) -> (instr, rest)
                      (options, rest) -> (combine options, rest)
    where combine [] = []
          combine [o] = o
          combine (o:os) = let instr = combine os in
                           let len = length instr in
                           [Split 1 (2 + length o)] ++ o ++ [Split (len + 1) (len + 1)] ++ instr
          read :: Regex -> String -> ([Regex], String)
          read acc [] = ([acc], [])
          read acc xs@(')':_)= ([acc], xs)
          read acc ('|':xs) = let (options, rest) = read [] xs in
                                 (acc:options, rest)
          read acc xs = let (instr, rest) = compilePart xs in
                        read (acc ++ instr) rest
                              
-- compile eigher a charcter, a wildcard, a character class, a
-- bracketed expression  or a back reference. Any of these may be
-- followed by a *, + or ?.
compilePart :: String -> (Regex, String)
compilePart ('(':xs) = let (instr, rest) = compileBrackets xs in
                        compileTail ([StartGroup 0] ++ instr ++ [EndGroup 0]) rest
compilePart ('[':'^':xs) = compileTail [MatchChars (Set.difference allLetters (Set.fromList cls))] rest
    where (cls, _:rest) = span (/=']') xs
compilePart ('[':xs) = compileTail [MatchChars (Set.fromList cls)] rest
    where (cls, _:rest) = span (/=']') xs
compilePart ('.':xs) = compileTail [MatchChars allLetters] xs
-- NOTE: Turning backrefs into .*s at the moment!!!!!
compilePart ('\\':ref:xs) = compileTail [BackRef $ (digitToInt ref) - 1] xs
compilePart (x:xs) = compileTail [MatchChars (Set.fromList [x])] xs
compilePart [] = ([],[])

-- Compile a bracketed sub-expression
compileBrackets (')':xs) = ([], xs)
compileBrackets xs = let (instr, rest) = compileOptions xs in
                     let (instr', rest') = compileBrackets rest in
                     (instr ++ instr', rest')
                     
-- Compile the tail part of a bit of a regex, this is either nothing,
-- *, + or ?
compileTail :: Regex -> String -> (Regex, String)
compileTail instr ('*':xs) = (((Split 1 (2 + length instr)) : instr) ++ [Split 1 (-(length instr))], xs)
compileTail instr ('?':xs) = ((Split 1 (1 + length instr)) : instr, xs)
compileTail instr ('+':xs) = (instr ++ [Split 1 (-(length instr))], xs)
compileTail instr xs = (instr, xs)
