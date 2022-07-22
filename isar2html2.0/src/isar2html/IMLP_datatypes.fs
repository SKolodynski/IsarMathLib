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

// TODO: check if we can replace all string list with string list
module IMLP_datatypes =

    /// named string list: very often used pair of string and string list
    type namedstrs = string*(string list)

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

    type Assumes = namedstrs list


    type LocaleItem = Fixes of NameNotation list
                    | Defs of Defines
                    | Assms of Assumes 

    type Locale = { localename: string;
                    inheritsFrom: namedstrs; // we support only one parent: locale1 = locale0 + [localeItems]
                    localeItems : LocaleItem list 
                    }

    type ProofUsingBy = { useunfold: string; // "using" or "unfolding"
                        usedprops: string list; // a list of references
                        useunfold1: string; // "using" or "unfolding", optional second clause
                        usedprops1: string list; // a list of references for the second clause
                        ptactic: string // a method: simp, auto, blast etc
    }

    type HenceThusStep = { henceorthus: string;
                        ttclaims: namedstrs list;
                        tttactic: string
                        }

    type Proof = UsingBy of ProofUsingBy | ByRule of string  | LongProof of ProofLongProof
    and ProofLongProof = { dash: bool;(* does it have a dash or not?*) proofSteps: ProofStep list }
    and ClaimProof = { cpclaims: namedstrs list;  cpproof: Proof }
    and ProofStep = LongReasoning of Reasoning*(MoreoverBody list)
                    | FixStep of string list
                    | LetStep of string*string*string  // variable name, optional subscript, definition
                    | Next
    and Reasoning = InitStep * ConnectedStep list
    and MoreoverBody = { mrvalso: string; // indicates if this is a moreover or also construct
                        mrvMrvs: Reasoning list;
                        ultimfinal: ProofCommand;
                        followup: ConnectedStep list }
    and InitStep = InitialStep of (string list)*ProofCommand 
                    | StepBlock of ProofStep list 
                    | Assume of namedstrs list 
                    | Note of string list
    and ConnectedStep = WithStep of (string list)*ProofCommand
                        | ThenStep of ProofCommand
                        | HenceThus of HenceThusStep
    and ProofCommand = PChaveShow of string*ClaimProof | PCbtain of string list*ClaimProof // the list of strings is the list of variables to obtain
    
    type Sublocale = {  sublocalename: string;
                        localename: string;
                        remapping: string list;
                        sublocproof: Proof
                        }

    type PropPremise = PropDefines of namedstrs list | PropAssumes of namedstrs list


    type Proposition = {    proptype: string; // may be "theorem", "lemma" or "corollary" 
                            context: string; // an optional locale
                            propname: string;
                            propprems: PropPremise list
                            claims:namedstrs list;
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
                        items: Item list
                        }

    type Theory = { header: string; 
                    name: string; 
                    imports: string list;
                    thintro: string;
                    thsections: Subsection list 
                    }

    type SimpProp = { sproptype: string;
                    scontext: string;
                    spropname: string;
                    sproprems: PropPremise list;
                    sclaims: namedstrs list;
                    sdeps: string list // names of dependencies
                    }

    type SimpleFormalItem = SimpleProp of SimpProp
                            | SimpleDef of string*string
                            | OtherSimpleItem // TODO: do we ever use that?

    ///  short version of formal item structure for storing information in the theorem database
    type FormalItemInfo = { fimTheoryName:string;
                            fimitem:SimpleFormalItem
                            }

    type TheoryInfo = { tiname: string; // redundant, but useful
                        titheory: Theory; // parsed theory
                        tideps: string list // a list of all dependencies in theory
                        }

    /// useful data extracted from all theories
    type KnowledgeBase = { kbformalitems: FormalItemInfo list; // common for all theories
                            kbtheories: TheoryInfo list // a list of information about theories
                            }
