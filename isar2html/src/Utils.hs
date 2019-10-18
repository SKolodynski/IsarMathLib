{-
	This file is part of isar2html - a tool for rendering IsarMathLib
	theories in in HTML.
    Copyright (C) 2008-2019  Slawomir Kolodynski

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}


module Utils
   where

import Data.List(isPrefixOf)

-- appToOnes f [(x,1), (y,1), (z,1), (a,0) , (b,0)]
appToOnes :: ([a] -> [a]) -> [(a,Int)] ->  [(a,Int)]
appToOnes f t = zip x (replicate (length x) (0::Int))
   where
   x = (f $ fst $ unzip t1) ++  (fst $ unzip t2 )
   (t1, t2) = span (\p -> (snd p) == 1) t

-- | zips a list with a list with repeated values
-- "abc" `zippedWith` 1 == [('a',1), ('b',1), ('c',1)]
zippedWith :: [a] -> b -> [(a,b)]
x `zippedWith` c = zip x (replicate (length x) c)

-- |   Applies a function to that part of the list that is between two marks
-- appBetween tf "$" "$" "abs$cde$ghi$cd$ab" == "abs***ghi**ab"
-- bug : does not work if the string starts with marks.
appBetween :: Eq a => ([a] -> [a]) -> [a] -> [a] -> [a] -> [a]
appBetween f beg end s = fst $ unzip (foldr g [(last s, 0::Int)] (init s))
   where
   --g :: Eq a => a -> [(a,Int)] -> [(a,Int)] -- does not compile with this
   g x xs | zb `isPrefixOf` xs = (x,0):(appToOnes f (drop (length beg) xs))
          | ze `isPrefixOf` xs = (x,1):(drop (length end) xs)
          | otherwise = ((x, snd $ head xs):xs)
            where
            zb = beg `zippedWith` (1::Int)
            ze = end `zippedWith` (0::Int)


-- |  a function that turns a list
-- into a list of pairs that indicate the "nesting level"
-- example  nestLevel '(' ')' "ab(c(de)f)" ==
-- [('a',0),('b',0),('(',1),('c',1),('(',2),('d',2),('e',2),(')',2),('f',1),(')',1),(')',0)]
nestLevel :: Eq a => a -> a -> [a] -> [(a, Int)]
nestLevel open close x =
   foldr nextelem [(lx, if lx == close then 1::Int else 0::Int)] (init x)
   where
      lx = last x
      nextelem c prev | c == close = (c, (snd $ head prev) + 1):prev
      nextelem c prev@((p,n):tprev) | p == open  = (c, n - 1):prev
      nextelem c prev              = (c, (snd $ head prev) ):prev

-- | applies a function only to parts of the list that
-- satisfy the given function test. It should be possible as usual
-- to avoid explicit recursion, but why? It is quite readable this way.

appToParts :: (a -> Bool) -> ([a] -> [a]) -> [a] -> [a]
appToParts testf transf [] = []
appToParts testf transf s | (testf $ head s) = (transf a) ++ (appToParts testf transf b)
   where (a,b) = span testf s
appToParts testf transf s = a ++ (appToParts testf transf b)
   where (a,b) = break testf s

-- | a test function for appToParts - replaces the first
-- component with stars

tf2 :: [(Char,Int)] -> [(Char,Int)]
tf2 si = zip (replicate (length si) '*') (snd $ unzip si)

-- | split on a substring
splitList :: Eq a => [a] -> [a] -> [[a]]
splitList sep = foldr f [[]]
   where
      f x (h:t) | sep `isPrefixOf` (x:h) = []:(drop n h):t
                | otherwise              = (x:h) : t
         where n = (length sep) -1

-- from Henning Thielemann at Haskell-cafe
replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace src dst =
    foldr (\x xs -> let y=x:xs
                    in  if isPrefixOf src y
                          then dst ++ drop (length src) y
                          else y) []

-- | multiple replacement, last replacement in the list is performed first!
-- to do: replace recursion with foldr
replaceAll :: Eq a => [ ([a],[a]) ] -> [a] -> [a]
replaceAll srcdest x = if (null srcdest) then x
                       else replace (fst h) (snd h) $ replaceAll (tail srcdest) x
                          where h = head srcdest

-- | removes specified elements from a list
remElems :: Eq a => [a] -> [a] -> [a]
remElems rems = filter (`notElem` rems)

-- | appends all elements of a
-- list except the last one with a given list
-- useful when intersperse not sufficient
append2Init :: [a] -> [[a]] -> [[a]]
append2Init s list = (map (++s) (init list)) ++ [last list]


-- | reads files from given a list of names
readFiles :: [String] -> IO [String]
readFiles = sequence . (map readFile)

-- writes a list of files given a list of
-- (name, contents) pairs
writeFiles :: [(String,String)] -> IO [()]
writeFiles = sequence . (map writeFilePair)
   where writeFilePair (n,c) = writeFile n c


-- | like lines, but also removes empty lines
nonemptylines :: String -> [String]
nonemptylines = (filter (/= "")) . lines

-- | like unlines, but does not add the last '\n'
sunlines :: [String] -> String
sunlines [] = []
sunlines s = init $ unlines s

-- | remove double new lines
rmdnl :: String -> String
rmdnl = replace "\n\n" "\n"
