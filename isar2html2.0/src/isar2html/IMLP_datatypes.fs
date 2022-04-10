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

[<AutoOpen>]

// TODO: check if we can replace all List<string> with string list
module IMLP_datatypes =

    type Definition = { defname: string; // maybe explicit or extracted from the actual definition
                        defcontext: string; //  an optional locale
                        deftypespec: string;
                        deflabel: string*bool; // optional, string is the label, Bool here means the presence of [simp] modifier
                        def: string 
    }

    type Abbreviation = {   abbname: string;
                            abbnotation: string; // string defining notation, like "_ ->F _ {in} _"
                            abbspec: string // the actual abbreviation (after the "where" keyword)
                            }

    type Defines = { locdefNameSimp:string*bool; // name may be with simp or not
                    locdef: string 
    }

    type NameNotation = { fixedName: string;
                        fixedNotation: string
    }

    type Assumes = List<string*List<string>>


    type LocaleItem = Fixes of List<NameNotation>
                    | Defs of Defines
                    | Assms of Assumes 

    type Locale = { localename: string;
                    inheritsFrom: string*List<string>; // we supportonly one parent: locale1 = locale0 + [localeItems]
                    localeItems : List<LocaleItem> 
                    }

    type ProofUsingBy = { useunfold: string; // "using" or "unfolding"
                        usedprops: List<string>; // a list of references
                        useunfold1: string; // "using" or "unfolding", optional second clause
                        usedprops1: List<string>; // a list of references for the second clause
                        ptactic: string // a method: simp, auto, blast etc
    }

    type HenceThusStep = { henceorthus: string;
                        ttclaims: List<string*List<string>>;
                        tttactic: string
                        }

    type Proof = UsingBy of ProofUsingBy | ByRule of string  | LongProof of ProofLongProof
    and ProofLongProof = { dash: bool;(* does it have a dash or not?*) proofSteps: List<ProofStep> }
    and ClaimProof = { cpclaims: List<string*List<string>>;  cpproof: Proof }
    and ProofStep = LongReasoning of Reasoning*List<MoreoverBody>
                    | FixStep of List<string>
                    | LetStep of string*string*string  // variable name, optional subscript, definition
                    | Next
    and Reasoning = InitStep * List<ConnectedStep>
    and MoreoverBody = { mrvalso: string; // indicates if this is a moreover or also construct
                        mrvMrvs: List<Reasoning>;
                        ultimfinal: ProofCommand;
                        followup: List<ConnectedStep> }
    and InitStep = InitialStep of List<string>*ProofCommand 
                    | StepBlock of List<ProofStep> 
                    | Assume of List<string*List<string>> 
                    | Note of List<string>
    and ConnectedStep = WithStep of List<string>*ProofCommand
                        | ThenStep of ProofCommand
                        | HenceThus of HenceThusStep
    and ProofCommand = PChaveShow of string*ClaimProof | PCbtain of List<string>*ClaimProof // the list of strings is the list of variables to obtain
    
    type Sublocale = {  sublocalename: string;
                        localename: string;
                        remapping: List<string>;
                        sublocproof: Proof
                        }

    type PropPremise = PropDefines of List<string*List<string>> | PropAssumes of List<string*List<string>>


    type Proposition = {    proptype: string; // may be "theorem", "lemma" or "corollary" 
                            context: string; // an optional locale
                            propname: string;
                            propprem: List<PropPremise>
                            claims:List<string*List<string>>;
                            propproof: Proof
    }

    type FormalItem = Def of Definition 
                    | Abbr of Abbreviation  
                    | Loc of Locale 
                    | Subloc of Sublocale 
                    | Prop of Proposition 

    type Item = { description: string;
                  formalItem: FormalItem
                  }

    type Subsection = { sectitle: string;
                        secIntro: string;
                        items: List<Item>
                        }

    type Theory = { header: string; 
                    name: string; 
                    imports: List<string>; 
                    thintro: string;
                    thsections: List<Subsection> 
                    }
    
