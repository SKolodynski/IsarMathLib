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

        /// any on a list, maybe there is a standard one?
        let any (p:'a->bool) (s:'a list) : bool =
             s |> List.map p |> List.contains true

        /// drops first and last of a list, like tail . init in Haskell, converts result to seq
        let dropEnds (s:'a list) :'a seq =
            s |> List.toSeq |>  Seq.take (s.Length-1) |> Seq.tail 

        /// a function that turns a list into a list of pairs that indicate the nesting level
        /// example: nestLevel '(' ')' "ab(c(de)f)" = 
        /// [('a',0);('b',0);('(',1);('c',1);('(',2);('d',2);('e',2);(')',1);('f',1);(')',0)]
        /// text: "ab(c(de)f)"
        /// levels 0011222211
        // Less functional than the Haskell version as that one uses init on list 
        // (all elements except the last) which F# does not have, but hopefully faster
        let nestLevel (op:char) (cl:char) (x:string) : ((char*int) list) =
            if x.Length=0 then []
            else 
                let res = Array.zeroCreate x.Length
                res.[0] <- if x.[0]=op then 1 else 0 
                for i in 1..x.Length-1 do
                    res.[i] <- if x.[i] = op then res.[i-1]+1
                                    else if x.[i-1] = cl then res.[i-1]-1
                                        else res.[i-1]
                Array.zip (x.ToCharArray()) res |> Array.toList
                
        /// removes specified chars from a string
        // TODO: rename to strip
        let remElems (rems:string) : string -> string =
             String.collect (fun c -> if Seq.exists ((=)c) rems then "" else string c)

        /// Applies a function to that part of the string that is between to marks given as substrings
        /// Example: 
        /// appBetween (fun x -> "  ") "$" "$" "abs$cde$ghi$cd$ab" == "abs  ghi  ab" 
        /// replaces all text between the dollar signs by two spaces. the dollar signs are removed
        /// and the function is expected to not see them.
        let rec appBetween (f:string->string) (start:string) (stop:string) (s:string) : string =
            let startPos = s.IndexOf start
            if startPos = -1 then s
            else 
                let stopPos=(s.[startPos+1..]).IndexOf stop 
                if stopPos = -1 then s
                else 
                    s.[..startPos] + (f s.[startPos+1..startPos+stopPos])
                        + (appBetween f start stop s.[startPos+stopPos+2..])

        /// remove double new lines
        let rmdnl (s:string) : string = s.Replace("\n\n","\n")
        
        /// concatenates lines
        // TODO: this is only somewhat needed in Haskell, redundant in F#
        let sunlines : (string list) -> string = String.concat ""