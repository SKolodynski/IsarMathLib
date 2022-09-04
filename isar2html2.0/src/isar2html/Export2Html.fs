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
    
    /// The function export2Html in this module takes a parsed 
    /// IsarMathLib theory and produces corresponding body of the HTML document.
    // TODO: maybe use Giraffe.view or smth to gnerate HTML instead of string manipulation
    module Export2Html =
        open IsarSym2Latex
        open Utils
        open ProcessThys

        /// makes a string boldface, also surrounds with spaces
        let bf (s:string) : string = "<b> " + s + " </b>"

        /// converts literal latex: surrounds with "\( \)"
        let convLatex (s:string) : string =  "\\(" + s + "\\)"

        /// converts the inner syntax to LaTeX. 
        let isar2latex (repls:(string*string) list) (s:string) : string =
            let formula = convBraces s 
                        |> replaceAll repls 
                        |> replace  ("\n","\\)\n\\(")
                        |> remElems "`?"
            "\\( " + formula + " \\)"

        /// chars allowed in literal texts that are not LaTeX. TODO: doe we need to allows space?
        let allowedInIds = Set.ofSeq "ABCDEFGHIJKLMNOPQRSTUVWXYabcdefghijklmnopqrstuvwxyzZ0123456789_. "

        /// checks if the text is an identifier. Those consist of alphanumeric characters and underscore
        // TODO: check if and why space is needed
        let isIdentifier  : string -> bool =
            String.forall (fun c -> allowedInIds.Contains c)

        /// makes text italic
        let it (s:string) : string = "<i>" + s + "</i>"

        /// converts literal text: "\<open> some text\<close>"
        let littext (repls:(string*string) list) (s:string) : string =
            if isIdentifier s then it s else isar2latex repls s

        /// makes a paragraph
        // TODO: doesn't it produce unclosed paragraphs?
        let par (s:string) : string =
            if s.StartsWith "<p>" then s else "<p>" + s + "</p>"

        /// makes a div to simulate paragraphs
        let pd (s:string) : string = "<div id=\"pardiv\" > " + s + "</div>"
        
        /// creates a heading
        let hd (s:string) : string =  "<h3>" + s + "</h3>"

        /// exports informal text
        let expInformalText (repls:(string*string) list) (s:string) : string =
            "<div class=\"inftext\">\n<p>"
            + ( appBetween (littext repls) "\\<open>" "\\<close>" s
                |> appBetween convLatex "$" "$"
                |> replace ("\n\n","</p>\n<p>"))
            + "</p>\n</div>\n"

        /// creates a floating slider
        let floatSlider (s:string) : string = "<span id=\"hintref\">" + s + "</span>"

        /// creates a slider
        let slider (tittle:string) (s:string) : string = 
            "<span id=\"hstrigger\" class=\"hideshow\" >"
            + tittle + "</span>\n"
            + "<div id=\"hscontent\" class=\"proof\" >" + s + "\n</div>\n"
        
        /// creates a link
        let tlink (target:string) (text:string) : string = 
            "<a href=\"" + target + "\">" + text + "</a>"

        /// creates an html option with a given name and value
        let hopt (nm:string) (value:string) : string =  nm + "=\"" + value + "\" "

        /// makes an anchor for jumping inside page
        /// to jum to lemma  cnvso do https://isarmathlib.org/Order_ZF_1.html#a_cnvso
        /// we cannot skip "a_" bc. it conflicts with something I don't remember (id?)
        let anchor (nm:string) : string =  "<div " + (hopt "id" ("a_" + nm)) + "></div> "

        /// makes formal item with a given name
        let mkformal (nm:string) (s:string) : string =
             "<div " + (hopt "class" "formal") 
             + (if nm.Length = 0 then "" else (hopt "id" nm)) + ">" 
             +  s + "\n</div>\n"

        /// renders a locale name in a theorem
        let inContext (s:string) : string =
            if s.Length>0 then "<b>(in</b> " + s + "<b>)</b> " else ""
        
        /// renders a reference hint that is displayed when a reference is clicked
        let refdiv (id:string) (s:string) : string =
            "<div id=\"" + id + "\"class=\"refhint\">" + s + "</div>"
        
        /// renders a reference that is used in simplified form. 
        // TODO: id looks the same, do we uniquefy it later?
        let refspan (s:string) : string =
            "<span id=\"hintref\">" + s + "</span>" 

        ///  makes unique every string occurence, adding the count as a div
        let uniquefy (id:string) (htmlstring:string) : string =
            let split = htmlstring.Split id // substrings ending with id, except the last one
            let n = (split.Length)-1 // number of occurences of id in htmlstring 
            if n=0 then htmlstring
            else 
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
            List.map uniquefy ids |> List.reduce (<<)

        /// appends a suffix to all elements of a list of strings except the last one
        // TODO: try to avoid using this by using String.concat suffix 
        let appendToInit (suffix:string) (ss:string list) : string list =
            match ss with
            | [] -> []
            | _ -> let (initss,lastss) = ss |> List.toArray |> Array.splitAt (ss.Length-1) in
                    Array.append (Array.map (fun s -> s+suffix) initss) lastss
                    |> Array.toList

        /// exports a single simple (unlabelled) claim
        let exportOneSimpleClaim (repls: (string*string) list) (claims:namedstrs) : string =
            List.map (isar2latex repls) (snd claims) |> String.concat ",  "

        /// exports simple form of claims
        let exportSimpleClaims (repls: (string*string) list) : (namedstrs list) -> string =
           List.map (exportOneSimpleClaim repls) >> String.concat (bf " and ")

        /// exports a single labelled claim
        let exportOneClaim (repls: (string*string) list) ((label,claims):namedstrs) : string =
            label + (if label="" then "" else ": ") + 
                (List.map (isar2latex repls) claims |> String.concat ", ")
        
        /// exports a sequence of labelled claims
        let exportClaims  (repls: (string*string) list) : (namedstrs list) -> string =
           List.map (exportOneClaim repls) >> String.concat (bf " and ") 
        
        /// exports a simplified form of a premise
        let exportPremiseSimple (repls:(string*string) list) (pp:PropPremise) : string =
            match pp with
            | PropDefines defs -> (bf "defines ") + (exportSimpleClaims repls defs) + "\n"
            | PropAssumes prms -> (bf "assumes ") + (exportSimpleClaims repls prms) + "\n"
        
        /// exports a list of premises in a simplified form
        // TODO: check if it is better to concat with spaces
        let exportPremisesSimple (repls:(string*string) list) (pps:PropPremise list) : string =
            List.map (exportPremiseSimple repls >> par) pps
            |> String.concat ""
        
        /// exports FormalItemInfo. 
        /// This a structure that holds a simplified information about a referenced formal item
        /// displayed in a grey rectangle on click
        let exportFormalItemInfo (repls:(string*string) list) (fif:FormalItemInfo) : string =
            let tn = fif.fimTheoryName
            match fif.fimitem with
            | SimpleProp sp->
                ( bf sp.sproptype) + " "
                + (inContext sp.scontext) 
                + (tlink (tn + ".html#a_" + sp.spropname) sp.spropname) + ": " 
                + (exportPremisesSimple repls sp.sproprems) 
                + (bf " shows ") + (exportSimpleClaims repls sp.sclaims)
            | SimpleDef (nm,d) -> ("Definition of " + nm + ":\n" + (isar2latex repls d) )
            | OtherSimpleItem -> " Other formal item " // TODO: check if we ever get here

        /// extracts part of the name after dot
        let afterDot (nm:string) = 
            if nm.Contains('.') 
                then nm.[1+nm.LastIndexOf('.')..]
                else nm
        
        /// extracts part of name before the paratheses
        let beforeParen (nm:string) : string = 
            if nm.Contains('(') 
            then nm.[..nm.IndexOf('(')-1]
            else nm

        /// checks if a reference is on the list of known theorems and and if so creates
        /// a div with the rendered simple form, otherwise returns an empty string
        let createRefDiv (mfii:Map<string,string>) (nm:string) : string =
            let nmAfterDot = afterDot nm
            let lookupNm = beforeParen nmAfterDot
            match mfii.TryFind(lookupNm) with
            | Some s -> refdiv nmAfterDot s
            | None -> ""
        
        /// takes the map of formal items and a name of theorem,
        /// returns a span that can be clicked on to show the hint
        /// only the part of the referenced theorem name that is after the last dot
        /// but before an opening parenthesis is taken
        /// e.g. if the referenced theorem name is topology0.lemma53(1)m then
        /// we look for lemma53 in the first argument
        let getRefSlider (mfii:Map<string,string>) (nm:string) : string =
            let nmAfterDot = afterDot nm
            let lookupNm = beforeParen nmAfterDot
            match mfii.TryFind(lookupNm) with
            | Some _ -> refspan nmAfterDot 
            | None -> nm
        
        /// extracts definition names from knowledge base
        let extractDefs : (FormalItemInfo list) -> string list =
            let chooser (fif:FormalItemInfo) : string option =
                match fif.fimitem with
                | SimpleDef (nm,d) -> Some nm
                | _ -> None
            List.choose chooser

        /// makes a link to a rendered theory for the theory name
        let thrylink (thn:string) : string = 
            "\n<p><a href=\"" + thn + ".html\">" + thn + "</a></p>\n"
        
        /// obtains names from various formal items
        /// TODO: check if field names can be the same as their type names.
        let getId (fitem:FormalItem) : string =
            match fitem with
            | Def definition -> definition.defname
            | Abbr abbreviation -> abbreviation.abbname
            | Loc locale -> locale.localename
            | Subloc sublocale -> ""
            | Prop proposition -> proposition.propname

        ///  exports locale item - "fixes", "defines" and "assumes"
        let exportLocaleItem (repls:(string*string) list) (litem:LocaleItem) =
            match litem with
            | Fixes nmnt -> ""
            | Defs defs -> (bf "defines") + (isar2latex repls defs.locdef) |> par
            | Assms cmls ->  (bf "assumes") + (exportClaims repls cmls) |> par
        
        /// exports a single name with notation, as used in the "fixes" locale item
        /// just write the name, the notation is evident from the "defines" line 
        let exportNameNotation (repls:(string*string) list) (nn:NameNotation) =
            isar2latex repls nn.fixedName + ", "

        /// exports a premise
        let exportPremise (repls:(string*string) list) (pp:PropPremise) =
            match pp with
            | PropDefines defs -> (bf "defines") + (exportClaims repls defs) |> par
            | PropAssumes prems -> (bf "assumes") + (exportClaims repls prems) |> par
        
        /// create a lookup table of descriptions of referenced theorems
        let getRefsInfo (repls:(string*string) list) : (FormalItemInfo list) -> Map<string,string> =
            let addKey fii = (getSFIname fii.fimitem,exportFormalItemInfo repls fii)
            List.map addKey >> Map.ofList

        /// puts a string in LaTeX subscript
        let exportSubScript (s:string) : string = 
            if s="" then "" else  "_{" + s + "}"

        /// export local reference. It may be a label or latex text in back quotes `
        // TODO check how it works. We should not have backquotes ever, formulas are surrounded by \<open> \<close>
        let exportLocRef  (repls:(string*string) list) (s:string) : string =
            if s[0] = '`' then isar2latex repls (s[1..s.Length-2]) else s

        /// exports init or connected proof local references, 
        /// wft can be "with", "from", "then"
        let exportLocRefs (repls:(string*string) list) (wft:string) (loclabs:string list) =
            (bf wft) + (List.map (exportLocRef repls) loclabs |> String.concat ", ") + " "

        ///  exports a proof
        let rec exportProof (repls:(string*string) list) (mfii:Map<string,string>) (proof:Proof) :string =
            match proof with
            |  UsingBy pub ->
                let export1 useunfold  usedprops =
                    (bf useunfold) + " "  + (usedprops |> List.map (getRefSlider mfii) |> String.concat ", ")
                if pub.usedprops.Length > 0 
                then 
                    export1 pub.useunfold  pub.usedprops
                    + if pub.usedprops1.Length > 0 then export1 pub.useunfold1  pub.usedprops1
                        else " "
                else " "
            | ByRule s -> 
               (bf "  by (rule ") + (getRefSlider mfii s) + ( bf ")") 
            | LongProof plp -> 
                slider "proof" ((plp.proofSteps 
                                |> List.map (exportProofStep repls mfii)
                                |> String.concat "\n"
                                |> rmdnl)
                                + "\n" + (bf "qed"))
        and exportProofStep (repls:(string*string) list) (mfii:Map<string,string>) (ps:ProofStep) : string =
            match ps with
            | LongReasoning (rs,mbs) ->
                (exportReasoning repls mfii rs) + "\n" +  (List.map (exportMoreoverBody repls mfii) mbs |> sunlines)

            | FixStep v -> 
                (bf "fix") + (List.map (isar2latex repls) v |> String.concat " ")
                |> pd
            | LetStep (v,s,d) ->
                (bf "let") + ( v + (exportSubScript s) + " = " + d |>  isar2latex repls)
                |> pd
            | Next -> bf "next" |> pd
        and exportReasoning (repls:(string*string) list) (mfii:Map<string,string>) ((is,css):Reasoning) : string =
            (exportInitStep repls mfii is) + "\n" 
            + (List.map (exportConnectedStep repls mfii) css |> sunlines)
        and exportMoreoverBody (repls:(string*string) list) (mfii:Map<string,string>) (mb:MoreoverBody) : string =
            let prepKeyWord s = ((bf mb.mrvalso) + " ") + s
            let ultfinal = if mb.mrvalso = "also" then "finally " else "ultimately " // TODO maybe consider mrvalso to be Also | Moreover
            (List.map ((exportReasoning repls mfii) >> prepKeyWord) mb.mrvMrvs |> String.concat "")
            + (bf ultfinal) + (exportProofCommand repls mfii (mb.ultimfinal)) + "\n" 
            + (List.map (exportConnectedStep repls mfii) mb.followup |> sunlines)
            |> pd
        and exportInitStep (repls:(string*string) list) (mfii:Map<string,string>) (is:InitStep) =
            match is with
            | InitialStep (loclabs,pc) -> 
                (if loclabs.Length>0 then exportLocRefs repls "from " loclabs else "")
                + (exportProofCommand repls mfii pc)
                |> pd
            | StepBlock pss -> 
                (List.map  (exportProofStep repls mfii) pss 
                    |> String.concat ""
                    |> slider "{")
                + bf "}"
            | Assume clms -> (bf "assume ") + exportClaims repls clms |> pd
            | Note refs -> 
                (bf "note ") + (List.map (exportLocRef repls) refs |> String.concat ", ")
                |> pd
        and exportConnectedStep (repls:(string*string) list) (mfii:Map<string,string>) (cs:ConnectedStep) =
            match cs with
            | WithStep (loclabs,pc) ->
                (exportLocRefs repls "with " loclabs) +  (exportProofCommand repls mfii pc)
                |> pd
            | ThenStep pc -> (bf "then ") + ( exportProofCommand repls mfii pc)
                            |> pd
            | HenceThus ht -> (bf ht.henceorthus) + " " + (exportClaims repls ht.ttclaims)
                            |> pd
        and exportProofCommand (repls:(string*string) list) (mfii:Map<string,string>) (pc:ProofCommand)  =
            match pc with
            | PChaveShow (hs,cp) -> (bf hs) + " " + (exportClaimProof repls mfii cp)
            | PCbtain (vars,cp) -> (bf "obtain" ) + (vars |> List.map (isar2latex repls) |> String.concat " ")
                                    + (bf "where ") +  (exportClaimProof repls mfii cp)
        and exportClaimProof (repls:(string*string) list) (mfii:Map<string,string>) (cp:ClaimProof) =
            (exportClaims repls cp.cpclaims) + (exportProof repls mfii cp.cpproof)

        let exportProposition (repls:(string*string) list) (mfii:Map<string,string>) (p:Proposition) : string =
            ((bf p.proptype) + " " + (inContext p.context) + p.propname + ":\n" |> par)
            + (List.map (exportPremise repls) p.propprems |> String.concat "")
            + (bf "   shows ") + ( exportClaims repls p.claims )
            + (exportProof repls mfii p.propproof)
            |> mkformal ""


        /// exports formal items
        let exportFormalItem (repls:(string*string) list) (mfii:Map<string,string>) (fit:FormalItem) =
            match fit with 
            | Abbr abbr ->  (bf  "Abbreviation" |> par) + (isar2latex repls abbr.abbspec |> par)
                            |> mkformal ""
            | Def def ->    ((bf  "Definition ")  + (if def.defcontext.Length=0 then "\n" else  " (in " + def.defcontext + ")") + "\n" |> par)
                            +  (isar2latex repls def.def |> par)
                            |> mkformal ""
            | Loc loc ->    let (parent,vars) = loc.inheritsFrom
                            (bf "Locale ") + loc.localename
                            + (if parent.Length=0 then "" else " = " + parent
                            + " " + (String.concat " " vars) + " +")
                            + (List.map (exportLocaleItem repls) loc.localeItems |> String.concat " ")
                            |> mkformal ""
            | Subloc subloc ->  (bf "Sublocale") + subloc.sublocalename + " &lt " + subloc.localename 
                                + (exportProof repls mfii subloc.sublocproof |> par)
                                |> mkformal ""
            | Prop prop ->  exportProposition repls mfii prop

        /// exports an item in a section
        let exportItem (repls:(string*string) list) (mfii:Map<string,string>) (it:Item) : string =
            (getId it.formalItem |> anchor) + "\n" + (expInformalText repls it.description) + "\n" 
            + (exportFormalItem repls mfii it.formalItem)
 
        /// exports a section
        let exportSubsection (repls:(string*string) list) (mfii:Map<string,string>) (s:Subsection) : string =
            (hd s.sectitle) + "\n" + (expInformalText repls s.secIntro) 
            + (List.map (exportItem repls mfii) s.items |> String.concat "\n")

        /// <summary>converts Isar theory to HTML markup, the main function of this module</summary>
        /// <param name="repls"> a list of string replacements in formal code to convert it to LaTeX</param>
        /// <param name="mfii"> a map of all known theorems rendered in simplified form</param>
        /// <param name="refs"> the list of all references in all proofs of the theory</param>
        /// <param name="th"> a parsed theory</param>
        /// <returns>The theory rendered in HTML</returns>
        let exportTheory (repls:(string*string) list) (mfii:Map<string,string>) (refs:string list) (th:Theory) : string =
            ( (bf "theory") + th.name + (bf "imports") + String.concat " " th.imports |> mkformal "")
            + ( bf "begin\n" |> mkformal "" )
            + ( expInformalText repls th.thintro )
            + ( List.map (exportSubsection repls mfii) th.thsections |> sunlines)
            + ( bf "end\n" |> mkformal "")
            + (List.map (createRefDiv mfii) refs |> String.concat "\n")
            |>  uniquefyids ["hstrigger"; "hscontent"; "hintref";"pardiv"]


        /// takes the template and the database of theorems and renders to html
        let exportTheories (templ:string) (kb:KnowledgeBase) : ((string*string) list) =
            let fi = kb.kbformalitems
            let repls = (extractDefs fi |> List.map def2replPair) @ inner2LatexSym
            let mfii = getRefsInfo repls fi
            let tinfos = kb.kbtheories
            let tlinks = tinfos |> List.map (fun (tinfo:TheoryInfo) -> thrylink (tinfo.tiname))
                                |> String.concat ""
            let expThr (tinfo:TheoryInfo) = 
                let exportedTheory = exportTheory repls mfii (tinfo.tideps) (tinfo.titheory)
                let  thHtml = templ |> replaceAll [ ("this is theory placeholder", exportedTheory)
                                                ; ("this is links placeholder", tlinks) ]
                ("isarhtml/" + tinfo.tiname + ".html", thHtml)
            List.map expThr tinfos
            
        

        

