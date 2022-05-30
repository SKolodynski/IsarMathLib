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

// DBG
open iml.IsarSym2Latex

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

// let teststr = "{{x}. x\<in>X}"
// printfn "%s" (convBraces teststr)
