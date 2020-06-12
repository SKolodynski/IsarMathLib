-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :  Slawomir Kolodynski 2007-2011
-- License     :  GPL 3
--
-- Maintainer  :  Slawomir Kolodynski
-- Stability   :  alpha
-- Portability :  Linux
--
-- | Tool for rendering IsarMathLib theories to DHTML. The main module with IO.
--
-----------------------------------------------------------------------------

module Main where

import IMLP_datatypes
import Utils
import IMLParser
import ProcessThys
import Export2Html


main = do
   thrylist   <- readFile "theories.conf"
   templ <- readFile "isar2html_template.html"
   --names <- return $ map extractTheoryName (nonemptylines $ remComments rml)
   names <- return $ map extractTheoryName (nonemptylines thrylist)
   templ <- readFile "isar2html_template.html"
   thstxt <- readFiles $ map ("../IsarMathLib/" ++) names
   kb <- return $ processTheories $ parseTheories $ zip names thstxt
   putStrLn $ "number of propositions: " ++ (show $ length $ filter isProposition $ kbformalitems kb)
   putStrLn $ "number of definitions: " ++ (show $ length $ filter isDefinition $ kbformalitems kb)
   thrsExported <- return $ exportTheories templ kb
   writeFiles thrsExported


-- | extract a name of the theory to load from a line in
-- the ROOT.ML file
extractTheoryName :: String -> String
extractTheoryName = (++ ".thy")

-- | removes comments - the text between (* and *)
remComments :: String -> String
remComments = tail . (appBetween (\s -> "") "(*" "*)") . (' ':)
