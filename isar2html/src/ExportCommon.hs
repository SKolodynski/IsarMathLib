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

module ExportCommon
   where

import Data.Char(isAlphaNum)

-- | This module groups functions useful for exporting to all formats

-- | checks if the text is an identifier. Those consist of alphanumeric characters and underscore
isIdentifier :: String -> Bool
isIdentifier = all isallowed
   where isallowed c = (isAlphaNum c) || (c == '_') || (c == '.') || (c == ' ')


