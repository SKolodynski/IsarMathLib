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

    module Export2Html =
        ///  makes unique every string occurence, adding the count as a div
        let uniquefy (id:string) (htmlstring:string) : string =
            let split = htmlstring.Split id // substrings ending with id, except the last one
            let n = (split.Length)-1 // number of occurences of id in htmlstring 
            let u =  Array.rev [|0..n-1|] // create id numbers, TODO: check if works without rev
                    |> Array.map (fun k -> id + (string k)) 
                    |> Array.zip split.[0..n-1] 
                    |> Array.map (fun (x,y) -> x+y)
                    |> Array.reduce (+)
            let countdiv = "\n<div id=\"par_" + id + "\" style=\"display:none\">" + (string n) + "</div>"
            (u+split.[n]) + countdiv

        /// composes some number of uniquefy for a list of id strings
        /// i.e. applies uniquefy for each id in the parameter to the given string
        let uniquefyids (ids: string list) : string -> string =
            List.map uniquefy ids |> List.reduce (>>)

        