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

open System.IO
open iml.IMLParser
open iml.ProcessThys
open iml.Export2Html
open iml.Utils

let names = File.ReadAllLines "theories.conf"
            |> Seq.filter (fun line -> 0 < String.length line) // Is it the best way to check if the string is empty?
            |> Seq.map (fun x -> x+".thy")            
let thstxt = Seq.map (fun name -> "../IsarMathLib/" + name |> System.IO.File.ReadAllText) names
let parsed = Seq.zip thstxt names |> Seq.toList |> parseTheories 
printfn "Parsed %i theories" parsed.Length 
let kb = processTheories parsed
printfn "number of propositions: %d, number of definitions: %d"
        (kb.kbformalitems |> List.filter isProposition |> List.length)
        (kb.kbformalitems |> List.filter isDefinition |> List.length)
let templ = File.ReadAllText "isar2html_template.html"
exportTheories templ kb |> writeFiles


// ----------------- debugging code, do not commit uncommented
// open iml.Utils
// let s = "ab+Binom(n,k) + c"
// let mn = "Binom"
// let templ = "{{$1}\\choose {2}}"
// let expanded = expMacro mn templ s 

// printfn "%s" expanded
    
// open FParsec
// let s = """interpretation comp_monoid:monoid0 "X\<longrightarrow>X" "Composition(X)" "comp2(X)"
//   unfolding monoid0_def comp2_def using Group_ZF_2_5_L2(1) by auto
// """

// let parseRes = run interpretation  s
// let res = match parseRes with
//             | Success(result, _, _) -> result
//             | Failure(errorMsg, _, _) -> 
//                 raise (ParsingError errorMsg)

// getDepsFromProof res |> printfn "%A" 
