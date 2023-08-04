(*
    This file is part of isar2html2.0 - a tool for rendering IsarMathLib
	theories in in HTML.
    Copyright (C) 2022-2023  Slawomir Kolodynski
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

// avoids  warning FS0040: 
// This and other recursive references to the object(s) being defined will be checked for initialization-soundness at runtime through the use of a delayed reference
#nowarn "40"
namespace iml

module IMLParser =

    open FParsec
    open System

    /// a utility making it easier to set a breakpoint
    let BP (p: Parser<_,_>) stream =
        let posBefore = getPosition stream
        let peekBefore = stream.PeekString 25
        let r = p stream 
        let peekAfter = stream.PeekString 25
        let posAfter = getPosition stream
        r 
    
    let keywords = [ "have"; "show"; "obtain"; "where"; "proof"; 
        "ultimately"; "finally"; "for"; "assume"; "let"; "then"; 
        "moreover"; "also"; "from"; "defines"; "fixes";"note"]


    /// parses nonempty text that does not contain any of the strings in the parameter and does not start with the backslash
    /// consumes the text until one of the given strings is encountered
    let pureText(ss:string list) : Parser<string,unit> =
        notFollowedBy (choice (List.map (pstring >> attempt) ss))  
        >>. manyCharsTill anyChar (choice (List.map (pstring >> attempt >> lookAhead) ss))

    
    /// -- like textBetween, but returns the enclosing delimiters
    let enclosedIn (start:string) (stop:string) : Parser<string,unit> =
        skipString start 
        >>. manyCharsTill anyChar (attempt (pstring stop)) 
        |>> (fun x -> start + x + stop)

    /// like textBetween, but ignores the section markers inside the start and stop tags 
    let betweenNest (start:string) (stop:string) : Parser<string,unit> =
        skipString start
        >>. manyStrings ((pureText [start;stop] <|> (attempt (enclosedIn start stop))))
        .>> skipString stop

    ///  parses and returns any text between start and stop
    let textBetween (start:string) (stop:string) : Parser<string,unit> =
        skipString start
        >>. manyCharsTill anyChar (attempt (pstring stop))

    /// parses and returns Isar comments
    let comment : Parser<string,unit> = textBetween "(*" "*)"

    /// a utility parser to make the FParser opt parser similar to Haskell Parsec option parser
    let poption (defVal:'a) (p:Parser<'a,unit>):  Parser<'a,unit> =
        opt p 
        |>> (fun optx -> defaultArg optx defVal)
     
    /// a modification of spaces1 that supports comments
    let whiteSpace1 :  Parser<unit,unit> =
        (attempt (spaces1 >>. poption "" comment >>. spaces)) <|>
            (spaces >>. poption "" comment >>. spaces1)

    /// a modification of whiteSpace1 that supports comments
    let whiteSpace :  Parser<unit,unit> =
        spaces >>. poption "" comment >>. spaces


    ///  parses and returns the informal text i.e. the text between
    ///  "text\<open>" and "\<close>"
    let informalText : Parser<string,unit> =
        pstring "text"
        >>. betweenNest "\\<open>" "\\<close>"
        

    /// parses the section line, returns the section title.
    let section : Parser<string,unit> =
        pstring "section"
        >>. whiteSpace
        >>. textBetween "\\<open>" "\\<close>"

    /// makes sure no forbidden word starts at the current position
    // TODO: improve the error message, we need to say which forbidden
    // word is here
    let notAnyOf (words:seq<Parser<'tok,unit>>) : Parser<unit,unit> =
        notFollowedByL (choice words) "unexpected token"

    /// a helper parser for manyTill - attempts given strings and succeeds
    /// when one of them parses. Does not consume input.
    let anyOf (ss:string list) : Parser<string,unit> =
        List.map (pstring >> attempt) ss |> choice |> lookAhead
    
    /// parses a word that consists of alphanumeric characters
    /// plus a list of some additional allowed characters given in the
    /// argument, but fails if that word is any of the keywords
    let alphaNumNotKeyword (chars:char list) : Parser<string,unit> =
         notAnyOf (List.map  (pstring >> attempt) keywords)
         >>. many1Satisfy (fun (c:char) -> isAsciiLetter c || isDigit c || List.contains c chars )

    /// Parses a valid theory,proposition or sublocale name, also labels.
    let itemName : Parser<string,unit> =
        alphaNumNotKeyword (Seq.toList "_.,()")

    /// like an the itemName, but we don't allow parentheses
    /// TODO: check if needed
    let pureItemName : Parser<string,unit> =
        alphaNumNotKeyword (Seq.toList "_.")

    /// Parses a variable name
    let varname : Parser<string,unit> =
        alphaNumNotKeyword (Seq.toList "_\\<>^'")

    /// Parses a quote reference. Starting from Isabelle 2007 one can
    /// refere to a fact by quoting, like "\<open>x\<in>B\<close>" instead 
    /// of by label like A1.
    /// TODO: check if and why we need backtics here in the return
    let literalQuote  : Parser<string,unit> =
        textBetween "\\<open>" "\\<close>" 
        |>> (fun x -> "`" + x + "`")

    ///  Parses a fact reference. Starting from Isabelle 2007 fact references 
    /// can be either item names or quotes
    /// TODO: change to factRef
    let labelRef : Parser<string,unit> = itemName <|> literalQuote
    
    /// Parses the inner logic text (the stuff in quotes in the formal part)
    let innerText : Parser<string,unit> = 
        (textBetween "\"" "\"") <|> (pstring "?thesis")

    /// parses a locale name in a proposition
    let incontext : Parser<string,unit> =  textBetween "(in "  ")"

    /// parses definition notation like
    /// (infixl "Xor" 66)
    /// ("Net(_)" 40)
    /// ("_ {is complete}")
    let defnotation : Parser<string,unit> =
        pipe4 
            (pchar '(' >>. poption "" (attempt (pstring "infixl") <|> pstring "infix"))
            (whiteSpace >>. textBetween "\"" "\"")
            (whiteSpace >>. poption "" (textBetween "[" "]"))
            (whiteSpace >>. poption "" (many1Satisfy isDigit) .>> whiteSpace .>> pchar ')')
            (fun fixity notation assocL assoc -> 
                if assocL.Length>0 then
                    "(" + fixity + " \"" + notation + "\" " +
                    "[" + assocL + "] " + assoc + ")" 
                else
                    "(" + fixity + " \"" + notation + "\" " + assoc + ")" )

    /// parses a type specification. Isabelle/ZF almost always does full type inference
    /// the only place where we need this is in some definition translated from Metamath
    let typespec : Parser<string,unit> =
        (pstring ":: ") >>. textBetween "\"" "\""

    /// parses the preamble of a definition, things like
    /// IsATopology ("_ {is a topology}" [90] 91) where
    /// IsComplete ("_ {is complete}") where
    let defpreamble : Parser<string*string*string*string,unit> =
        pipe4
            (poption "" incontext)
            (whiteSpace >>. itemName)
            (whiteSpace >>. poption "" typespec)
            (whiteSpace >>. poption "" defnotation .>> whiteSpace .>> pstring "where")
            (fun contxt name ts spec -> (contxt,name,ts,spec))
            
    /// parses an assertion label with a possible "simp" modifier.
    /// The parser returns a string which is the label and True 
    /// if the simp was present or False if not
    let labelsimp : Parser<string*bool,unit> =
        pipe2
            (varname .>> whiteSpace)
            (poption "" (pstring "[simp]") .>> pchar ':')
            (fun dn s -> (dn,s<>""))

    /// parses abbreviations
    let abbreviation : Parser<FormalItem,unit> =
        pipe3
            (pstring "abbreviation" >>. whiteSpace >>. pureItemName)
            (whiteSpace >>. textBetween "(\"" "\")")
            (whiteSpace >>. pstring "where" >>. whiteSpace >>. innerText)
            (fun nm nt d -> Abbr { abbname = nm; abbnotation = nt; abbspec = d })

    /// parses definitions. Note we require a space before \<equiv> in the definition
    let definition : Parser<FormalItem,unit> =  
        let extrName = Seq.takeWhile (fun c -> c<>' ') 
                    >> Seq.takeWhile (fun c -> c<>'(') 
                    >> String.Concat // is this really the best way? Requires opening System
        pipe3
            (pstring "definition" >>. whiteSpace >>. poption ("","","","") defpreamble)
            (whiteSpace >>. poption ("",false) labelsimp)
            (whiteSpace >>. innerText)
            (fun (contxt,name,tspec,spec) ls d -> 
                let actName = if name <> "" then name else extrName d
                Def { defname = actName; defcontext = contxt; deftypespec = spec; deflabel = ls; def = d} )
    
    /// parses a list of variables with a "for" clause that appeared in Isabelle 2009.
    /// looks like "K A M for K A M". This is the only form we support in the parser,
    /// - a list of variables, then "for" then another list of variables that we ignore
    /// TODO: we should not be ignoring the other list as this breaks 
    /// the principle that we should be able to reconstruct the document 
    /// from the parsed form
    let renamedvars : Parser<string list,unit> =
        sepEndBy1 varname whiteSpace .>> pstring "for" .>> whiteSpace .>> sepEndBy1 varname whiteSpace

    /// parses a part of locale definition that defines inheritance from another locale
    let inheritedFrom : Parser<namedstrs,unit> =
        pipe2
            (itemName .>> whiteSpace)
            (poption [] renamedvars .>> whiteSpace .>> pchar '+')
            (fun parent vars -> (parent,vars))

    /// parses a variable name with its notation
    let namenotation : Parser<NameNotation,unit> =
        pipe2
            (varname .>> whiteSpace)
            (poption "" (textBetween "(" ")"))
            (fun iname notation -> {fixedName = iname; fixedNotation = notation})

    /// parses a "fixes" locale item
    let locItemfixes : Parser<LocaleItem,unit> =  
        pstring "fixes" >>. whiteSpace >>. sepEndBy1 namenotation whiteSpace |>> Fixes

    /// parses a "defines" locale item
    let locItemDefines : Parser<LocaleItem,unit> =
        pipe2
            (pstring "defines" >>. whiteSpace >>. labelsimp)
            (whiteSpace >>. textBetween "\"" "\"")
            (fun ls ld -> Defs {locdefNameSimp = ls; locdef = ld} )

    /// parses a statement label
    let statLabel :  Parser<string,unit> =
        itemName .>> pchar ':' 

    /// parses labelled statement list
    /// like A1: "a \<in> A"  "b \<in> B"
    let labelledStatList : Parser<namedstrs,unit> = 
            (poption "" statLabel) .>>. (whiteSpace >>. sepEndBy1 innerText whiteSpace)
            

    /// parses a list of labelled statement lists
    /// TODO: maybe create a type of decorated string list
    /// TODO: and is ignored in the parsed form, fix?
    let listLabStatLists : Parser<(namedstrs) list,unit> = 
        sepBy1 labelledStatList (whiteSpace >>. attempt (pstring "and") >>. whiteSpace)
        
    /// parses an "assumes" locale item
    let locItemAssumes :  Parser<LocaleItem,unit> =
        pstring "assumes" >>. whiteSpace >>. listLabStatLists |>> Assms
            
    /// parses a locale item: "fixes", "defines" or "assumes"
    let localeItem :  Parser<LocaleItem,unit> =
         locItemfixes <|> locItemDefines <|> locItemAssumes

    /// parses locale
    let locale : Parser<FormalItem,unit> =
        pipe3
            (pstring "locale" >>. whiteSpace >>. itemName)
            (whiteSpace >>. pchar '=' >>. whiteSpace >>. poption ("",[]) inheritedFrom)
            (whiteSpace >>. sepEndBy1 localeItem whiteSpace)
            (fun n inhf li -> Loc { localename = n; inheritsFrom = inhf; localeItems = li})

    /// parses a subscript in the let expression
    let subscript : Parser<string,unit> =
        pstring "\\<^sub>" >>. varname 


    /// parses a "let" directive
    let letstep : Parser<ProofStep,unit> =
        pipe3
            (pstring "let ?" >>. varname)
            (poption "" subscript)
            (pstring  " = " >>. innerText)
            (fun v s d -> LetStep (v,s,d))

    /// parses a "fix" directive
    let fixstep : Parser<ProofStep,unit> =
        pstring "fix " >>. sepEndBy1 varname whiteSpace |>> FixStep

    /// parses the "next" as a proof step
    let next : Parser<ProofStep,unit> =
        pstring "next" |>> fun _ -> Next

    /// parses local references starting from "from" or "with" or "note"
    let locrefs (s:string) :  Parser<string list,unit> =
        pstring s >>. whiteSpace >>. sepEndBy1 labelRef whiteSpace

    ///  parses a "note" statement
    let note : Parser<InitStep,unit> =
         locrefs "note" |>> Note
    
    /// parses an "assume" statement
    let assume : Parser<InitStep,unit> =
        pstring "assume" >>. whiteSpace >>. listLabStatLists |>> Assume

    /// parses a tactic
    let tactic : Parser<string,unit> =
        attempt (pstring "simp_all") <|> pstring "simp" <|> pstring "auto" <|> pstring "blast" <|>
        attempt (pstring "fast") <|> pstring "force"

    /// parses a short proof that has only a tactic in it
    let shortProofByTac : Parser<Proof,unit> =
        pstring "by" >>. whiteSpace >>. tactic 
        |>>  fun tac -> UsingBy { useunfold = ""; usedprops = []; useunfold1 = "";usedprops1 = []; ptactic = tac }

    /// parses "by rule(... )" type of proof
    let shortProofByRule : Parser<Proof,unit> =
        pstring "by (rule " >>. pureItemName .>> pchar ')' 
        |>> fun r ->  ByRule r

    /// parses a short proof that has "using" or "unfolding" keyword with references,
    /// stops on either the "by" or the next "using" or "unfolding"
    let shortProofRef : Parser<namedstrs,unit> =
        pipe2
            (attempt (pstring "using") <|> pstring "unfolding")
            (whiteSpace >>. manyTill (itemName .>> whiteSpace) (anyOf ["using";"unfolding";"by"]))
            (fun meth itms -> (meth,itms)) 

    /// parses short proof that has "using" or "unfolding" (or both) 
    /// keyword with references
    let shortProofRefTac : Parser<Proof,unit> =
        pipe3
            shortProofRef
            (whiteSpace >>. poption ("",[]) shortProofRef)
            (whiteSpace >>. pstring "by" >>. whiteSpace >>. tactic)
            (fun (meth,itms) (meth1,itms1) tac -> 
                UsingBy {useunfold = meth; usedprops = itms; useunfold1 = meth1; usedprops1 = itms1; ptactic = tac})

    /// parses a False constant. This is treated as a kind of claim
    let claimfalse : Parser<(namedstrs) list,unit> =
        pstring "False" |>> (fun s -> [("",[s])])

    let letOrFixStep : Parser<ProofStep,unit> = attempt (letstep <|> fixstep)

    ///  parses a proof (Parser<Proof,unit>) 
    // in F# explicit eta-conversion is sometimes necessary for deeply recursive objects
    // see https://stackoverflow.com/questions/1084374/parsing-lazy-initialization-and-mutually-recursive-monads-in-f
    let rec proof s = 
        (longproof <|> (attempt shortProofByTac) <|> shortProofByRule <|> shortProofRefTac) s

    /// parses a long proof Parser<Proof,unit>
    and longproof s  =
        (pipe2
            (pstring "proof" >>. whiteSpace >>. poption ' ' (pchar '-'))
            (whiteSpace >>. (sepEndBy1 proofstep whiteSpace) .>> (pstring "qed"))
            (fun d ps ->  LongProof { dash = (d='-'); proofSteps = ps })) s
    
    /// Parser<ProofStep,unit>
    and proofstep s =
        (letstep <|> (attempt fixstep) <|> (attempt longreasoning) <|> next) s
    
    and longreasoning : Parser<ProofStep,unit> =
        pipe2
            (reasoning .>> whiteSpace)
            (sepEndBy ((attempt (moreoverbody "also")) <|>  (moreoverbody "moreover"))  whiteSpace)
            (fun ir mbs -> LongReasoning (ir,mbs))
    
    and reasoning : Parser<Reasoning,unit> =
        pipe2
            (initStep .>> whiteSpace)
            (sepEndBy connectedStep whiteSpace)
            (fun is cs -> Reasoning (is,cs))

    and initStep : Parser<InitStep,unit> =
        stepblock <|> assume <|> note <|> inference
    
    and stepblock : Parser<InitStep,unit> =
        (pchar '{' >>. whiteSpace >>. sepEndBy1 proofstep whiteSpace .>> pchar '}')
        |>> StepBlock

    and inference : Parser<InitStep,unit> =
        pipe2
            (poption [] (locrefs "from"))
            (whiteSpace >>. proofcom)
            (fun lr pc -> InitialStep (lr,pc))
    
    and proofcom : Parser<ProofCommand,unit> =
        proofcomobtain <|> proofcomhaveshow
    
    and proofcomobtain :  Parser<ProofCommand,unit> =
        pipe2
            (pstring "obtain" >>. whiteSpace >>. sepEndBy varname whiteSpace)
            (pstring "where" >>. whiteSpace >>. claimproof)
            (fun vars cp -> PCbtain (vars,cp))
         
    and claimproof :  Parser<ClaimProof,unit> =
        pipe2
            ((attempt listLabStatLists) <|> claimfalse)
            (whiteSpace >>. proof)
            (fun c p -> { cpclaims = c;  cpproof = p })

    and proofcomhaveshow : Parser<ProofCommand,unit> =
        pipe2
            (pstring "have" <|> pstring "show")
            (whiteSpace >>. claimproof)
            (fun hs cp -> PChaveShow (hs,cp))
    
    // TODO: check if the last attempt is needed
    and connectedStep : Parser<ConnectedStep,unit> =
        withstep <|> attempt thenstep <|> attempt hencethus
    
    and withstep : Parser<ConnectedStep,unit> =
        pipe2
          (locrefs "with")
          (whiteSpace >>. proofcom)
          (fun lr pc -> WithStep (lr,pc))  

    and thenstep : Parser<ConnectedStep,unit> =
        pstring "then" >>. whiteSpace >>. proofcom |>> ThenStep

    and hencethus : Parser<ConnectedStep,unit> =
        pipe3
            (pstring "hence" <|> pstring "thus")
            (whiteSpace >>. ((attempt listLabStatLists) <|>  claimfalse))
            (whiteSpace >>. pstring "by" >>. whiteSpace >>. tactic)
            (fun ht c tac -> HenceThus {henceorthus = ht;ttclaims = c;tttactic = tac})

    and moreoverbody (s:string) :  Parser<MoreoverBody,unit> =
        pipe3
          (sepEndBy1 (moreoveritem s) whiteSpace)
          ((if s="also" then pstring "finally" else pstring "ultimately") >>. whiteSpace >>. proofcom) 
          (whiteSpace >>. sepEndBy connectedStep whiteSpace)
          (fun items pc cs -> { mrvalso = s;
                                mrvMrvs = items;
                                ultimfinal = pc;
                                followup = cs })

    and moreoveritem (s:string) : Parser<Reasoning,unit> = 
        pstring s >>. whiteSpace >>. reasoning

    /// parses a sublocale     
    let sublocale : Parser<FormalItem,unit> =
        pipe5
            (pstring "sublocale" >>. whiteSpace >>. pureItemName .>> whiteSpace .>> pchar '<')
            (poption "" (attempt (whiteSpace >>. statLabel)))
            (whiteSpace >>. pureItemName)
            (whiteSpace >>. manyTill (itemName .>> whiteSpace) (anyOf ["using";"unfolding";"proof";"by"]))
            (whiteSpace >>. proof)
            (fun sln lbl ln itms pr -> Subloc { sublocalename = sln;
                                            label = lbl;
                                            localename = ln;
                                            remapping = itms;
                                            sublocproof = pr
                                            })
    /// parses an interpretation
    let interpretation : Parser<FormalItem,unit> =
        pipe4
            (pstring "interpretation" >>. whiteSpace >>. pureItemName .>> whiteSpace .>> pchar ':')
            (whiteSpace >>. pureItemName)
            (whiteSpace >>. manyTill (innerText .>> whiteSpace) (anyOf ["using";"unfolding";"proof";"by"]))
            (whiteSpace >>. proof)
            (fun iname target pars pr -> 
                Interpretation {    interprname = iname
                                    target = target
                                    parameters = pars
                                    interprproof = pr
                                })

    /// various synonyms of theorem we use in IsarMathLib
    let propSynonim : Parser<string,unit> =
        pstring "theorem" <|> pstring "lemma" <|> pstring "corollary"

    /// parses an "assumes" statement
    let premassumes :  Parser<PropPremise,unit> =
        pstring "assumes" >>. whiteSpace >>. listLabStatLists |>> PropAssumes
    
    /// parser a "defines" statement
    let premdefines :  Parser<PropPremise,unit> =
        pstring "defines" >>. whiteSpace >>. listLabStatLists |>> PropDefines
    
    ///  parses "assumes" and "defines" statements in the premises
    let premises : Parser<PropPremise list,unit> =
        sepEndBy (premassumes <|> premdefines) whiteSpace

    /// parses a proposition
    let proposition : Parser<FormalItem,unit> =
        pipe5
            ((propSynonim .>> pchar ' ') .>>. poption "" incontext)
            (whiteSpace >>. itemName .>> pchar ':')
            (whiteSpace >>. poption [] premises)
            (pstring "shows" >>. listLabStatLists)
            (whiteSpace >>. proof)
            (fun (t,c) n ps cl pr -> Prop { proptype = t; // may be "theorem", "lemma" or "corollary" 
                                            context = c; // an optional locale
                                            propname = n;
                                            propprems = ps;
                                            claims = cl;
                                            propproof = pr
                                        })

    /// parses formal item with its description
    let itemWdescription : Parser<Item,unit> =
        pipe2
            informalText
            //(whiteSpace >>. (abbreviation <|> definition <|> interpretation <|> sublocale <|> attempt locale <|> proposition))
            (whiteSpace >>. choice [abbreviation;definition;interpretation;sublocale;attempt locale;proposition])
            (fun desc fitem -> { description = desc; formalItem = fitem}) 


    /// parses a Subsection
    let subsection : Parser<Subsection,unit> =
        pipe3
            (textBetween "subsection\\<open>" "\\<close>")
            (whiteSpace >>.  informalText)
            (whiteSpace >>. sepEndBy itemWdescription whiteSpace)
            (fun st si its -> { sectitle = st; secIntro = si; items = its })

    /// parses a theory. We have to parse imports separated by the space characters
    /// rather than whiteSpace bc. otherwise we consume "begin" which is after a newline
    let theoryParser :  Parser<Theory,unit> =
        pipe5
            (whiteSpace >>. section)
            (whiteSpace >>. pstring "theory" >>. whiteSpace >>. itemName)
            (whiteSpace >>. pstring "imports" >>. whiteSpace >>. sepBy1 itemName (pchar ' '))
            (whiteSpace >>. pstring "begin" >>. whiteSpace >>. informalText)
            (whiteSpace >>. sepEndBy1 subsection whiteSpace .>> pstring "end")
            (fun s n importlist i ss -> { header = s; name = n; imports = importlist; thintro = i; thsections = ss})

    
    exception ParsingError of string

    /// parses a list of theory texts
    /// TODO - parse in paralel
    let parseTheories (txts:(string*string) list) : Theory list  =
        let res2val (txt,n) = 
            let r = run theoryParser txt
            match r with
                | Success(result, _, _) -> result
                | Failure(errorMsg, _, _) -> 
                                            let msg = $"{n}:{errorMsg}"
                                            printfn "%s" msg 
                                            raise (ParsingError "")
                                            
        List.map res2val txts
        
