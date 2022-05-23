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
            |> thenAppend (List.toSeq sp |>  Seq.take (sp.Length-1) |> Seq.tail) 
            |> thenAppend (seq {(' ', n); ('}', n)})
            |> Seq.toList

        /// returns true if a character is not a letter or space or curly brace
        let isNotAlphaSpaceBrace (c:char,n:int) : bool = 
            not (Char.IsLetter c || c=' ' || c='{' || c='}')
            
        
        