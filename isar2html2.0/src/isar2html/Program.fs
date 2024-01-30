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

let nameValid (line:string) =
    let trimmed = line.Trim()
    if 0<String.length trimmed then Some (trimmed + ".thy") else None
let names = File.ReadAllLines "theories.conf"
            |> Seq.choose nameValid
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
    
// open FParsec
// let s = """locale ring2 = ring0 +
//   fixes I
//   assumes idealAssum: "I\<triangleleft>R"

//   fixes quot ("R\<^sub>I")
//   defines quot_def [simp]: "R\<^sub>I \<equiv> QuotientBy(I)"

//   fixes qrel ("r\<^sub>I")
//   defines qrel_def [simp]: "r\<^sub>I \<equiv> QuotientGroupRel(R,A,I)"
// """

// let parseRes = run locale  s
// let res = match parseRes with
//             | Success(result, _, _) -> result
//             | Failure(errorMsg, _, _) -> 
//                 raise (ParsingError errorMsg)

// res |> printfn "%A" 
