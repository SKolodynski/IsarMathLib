(*
    This file is part of isar2html2.0 - a tool for rendering IsarMathLib
	theories in in HTML.
    Copyright (C) 2022  Slawomir Kolodynski
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
*)

namespace iml

    module IsarSym2Latex =
        open Utils
        open System
        
        
        /// converts a predicate like "{is a topology}"
        let convPredicate (n:int) (sp:(char*int) list) : (char*int) list =
            (Seq.zip "\\text{ " (Seq.replicate 7 n)) 
            |> thenAppend (dropEnds sp) 
            |> thenAppend (seq {(' ', n); ('}', n)})
            |> Seq.toList

        /// returns true if a character is not a letter or space or curly brace
        let isNotAlphaSpaceBrace (c:char,n:int) : bool = 
            not (Char.IsLetter c || c=' ' || c='{' || c='}')

        /// takes a list of (character, nest level) pairs and decides
        /// if this represents a set comprehension. Set comprehensions 
        /// are heuristically recognized as having length less than 11
        /// or characters that are not letters, spaces of braces.
        /// TODO: this is a crappy way, try to find a better one.
        let isSetCompr (s:(char*int) list) : bool =
            s.Length<11 || (any isNotAlphaSpaceBrace s)

        /// converts a string with level info representing a set comprehension
        ///  or a predicate starting from given nest level
        /// assumes that the input starts with ('{',n) and ends with ('}',n)
        // TODO: add spaces after \{ and \}, it's LaTeX safer this way
        let rec convTextsLevel n  =
            appToParts (snd >> (<) n) (convSetComprPred n) // ((<) n) x evaluates to  n < x 
        and convSetComprPred (n:int) (sp:(char*int) list) : (char*int) list =
             if isSetCompr sp then convSetCompr n sp else convPredicate n sp
        and convSetCompr n sp =
            seq [('\\',n);('{',n)]
            |> thenAppend (convTextsLevel (n+1) sp |> dropEnds)
            |> thenAppend (seq [('\\',n);( '}', n)])
            |> Seq.toList
       
        /// converts expressions of the form "{...}" in the inner logic. 
        /// This might be a set comprehension, a singleton or a predicate like "{is a topology}"
        /// with similar expressions inside that need to be converted as well
        let convBraces : string -> string =
            nestLevel '{' '}' >> convTextsLevel 0 >> List.unzip 
            >> fst >> List.map string >> List.reduce (+)
        
        

            

            
        
        