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

    module Utils =

        /// replace a string by a string in a string. There is a standard function  
        /// for that but we want one that can be curied
        let replace ((src,dest):string*string) (s:string) : string = s.Replace(src,dest)
             
        /// multiple replacement, last replacement in the list is performed first!
        let replaceAll (srcdest: (string*string) list)  : string -> string=
            srcdest |> List.map replace |> List.reduce (<<)
        
        /// span splits a list into a part that satisfies a predicate and the rest
        /// (like Haskell's span)
        let span (p:'a->bool) (s:'a list) : ('a list)*('a list) =
            (List.takeWhile p s,List.skipWhile p s)
        
        /// nspan splits a list into a part that doe not satisfies a predicate and the rest
        /// like Haskell's break, but break is reserved
        let nspan (p:'a->bool) : ('a list) -> ('a list)*('a list) =
            span (p>>not)

        /// applies a function only to parts of the list that satisfy the given test function
        let rec appToParts (testf:'a->bool) (transf:('a list)->('a list)) (s:'a list) : 'a list =
            if s.IsEmpty then s
            elif testf s.Head then
                let (a,b) = span testf s
                (transf a) @ (appToParts testf transf b)
            else
                let (a,b) = nspan testf s
                a @ (appToParts testf transf b)

        /// like Seq.append but with parameters flipped for better piping
        let thenAppend (x:'a seq) (y:'a seq) : 'a seq = Seq.append y x
