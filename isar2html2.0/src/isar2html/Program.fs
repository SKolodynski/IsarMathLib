open System.IO
open iml.IMLParser

let names = File.ReadAllLines(@"theories.conf")
            |> Seq.filter (fun line -> 0 < String.length line) // Is it the best way to check if the string is empty?
            |> Seq.map (fun x -> x+".thy")            
let thstxt = Seq.map (fun name -> "../IsarMathLib/" + name |> System.IO.File.ReadAllText) names
let parsed = Seq.zip thstxt names |> Seq.toList |> parseTheories 
printfn "%s" $"Parsed {parsed.Length} theories"


//open FParsec
//let str = System.IO.File.ReadAllText "../IsarMathLib/test.thy"
//printfn "loaded %d characters" str.Length

// let str = """assume "0 \<in> leftUniformity"
//    hence False by auto"""

// printfn "parsing %s" str
// run reasoning str |> printfn "%A"
