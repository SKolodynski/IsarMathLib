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

    /// this module processes information obtained by parsing theory files. 
    /// For now it extracts the list of definitions and theorems from the theories.
    module ProcessThys = 

    /// F# does not have concatMap built in
        let concatMap f m = 
            List.concat( List.map (fun x -> f x) m )

    /// gets all dependencies from a proof
    /// TODO: definitions in unfolding
        let rec getDepsFromProof : Proof -> string list =
            function
            | UsingBy { useunfold=_;
                        usedprops=d;
                        useunfold1=_; 
                        usedprops1=d1;
                        ptactic=_} -> d @ d1
            | ByRule s -> [s]
            | LongProof { dash=_; proofSteps=pss} -> concatMap getDepsFromProofStep pss
        
        and getDepsFromProofStep : ProofStep -> string list =
            function
            | LongReasoning (r,mbs) ->
                (getDepsFromReasoning r) @ (concatMap getDepsFromMoreoverBody mbs)
            | _ -> []
        
        /// gets dependencies from reasoning
        and getDepsFromReasoning ((is,css): Reasoning) : string list =
            (getDepsFromInitStep is) @ (concatMap getDepsFromConnectedStep css)
        /// gets dependencies from InitStep
        and getDepsFromInitStep : InitStep -> string list =
            function
            | InitialStep (_,pc) -> getDepsFromProofCommand pc
            | _ -> []
        /// gets dependencies from a MoreoverBody
        and getDepsFromMoreoverBody { mrvalso=_;
                                    mrvMrvs=rss;
                                    ultimfinal=pc;
                                    followup=css} : string list =
                (concatMap getDepsFromReasoning rss) @ 
                (getDepsFromProofCommand pc) @
                (concatMap getDepsFromConnectedStep css)
        /// gets dependencies from a ConnectedStep
        and getDepsFromConnectedStep :  ConnectedStep -> string list =
            function
            | WithStep (_,pc) -> getDepsFromProofCommand pc
            | _ -> []
        /// gets dependencies from a ProofCommand
        and getDepsFromProofCommand :  ProofCommand -> string list =
            function
            | PChaveShow (_,cp) -> getDepsFromClaimProof cp
            | PCbtain (_,cp) -> getDepsFromClaimProof cp
        /// gets dependencies from a ClaimProof
        and getDepsFromClaimProof {cpclaims=_;cpproof=p} : string list = 
            getDepsFromProof p

        /// get dependencies from a proposition (theorem, lemma or corollary)
        let getDepsFromProposition (prop:Proposition) : string list =
            getDepsFromProof prop.propproof

        /// Converts a formal item to a a simplified form.
        let formal2simple : FormalItem -> SimpleFormalItem =
            function
            | Def d ->  SimpleDef (d.defname,d.def)
            | Prop prop -> SimpleProp { sproptype=prop.proptype;
                                                    scontext=prop.context;
                                                    spropname=prop.propname;
                                                    sproprems=prop.propprems;
                                                    sclaims=prop.claims;
                                                    sdeps=getDepsFromProposition prop
                                                    }
            | _ -> OtherSimpleItem

        /// gets all the formal items in th simple form from a section
        let getThmsDefsFromSec (sbs:Subsection) : SimpleFormalItem list =
            List.map (fun (im:Item) -> formal2simple im.formalItem ) sbs.items

        /// converts a list of simple formal items into a list of
        /// formal item infos by adding the name of theory
        let addTheoryName (nme:string) (item:SimpleFormalItem) : FormalItemInfo =
            { fimTheoryName = nme; fimitem = item }

        /// gets all formal items from a theory in simple form
        let getThmsDefsFromThry (t:Theory) : FormalItemInfo list =
            concatMap getThmsDefsFromSec t.thsections |> List.map (addTheoryName t.name)

        let getThmsDefsFromTheories (ts:Theory list) : FormalItemInfo list =
            concatMap getThmsDefsFromThry ts

        /// a helper function: skips all characters in a string until the last dot
        let skipUntilAfterDot (s:string) : string =
            let dotpos=s.LastIndexOf '.'
            if dotpos=(-1) then s else (s.Remove (1+dotpos))

        /// get dependencies from formal Item
        let getDepsFromFormalItem : FormalItem -> string list =
            function
            | Prop p -> getDepsFromProposition p
            | _ -> []

        /// get dependencies from a Subsection
        let getDepsFromSubsection (sbs:Subsection) : string list =
            concatMap (fun item -> getDepsFromFormalItem item.formalItem) sbs.items

        /// obtains dependecies from a Theory
        let getDepsFromTheory (t:Theory) : string list =
            let nmAfterDot = skipUntilAfterDot t.name
            concatMap getDepsFromSubsection t.thsections


        /// extracts useful information from a single theory
        let getTheoryInfo (t:Theory) : TheoryInfo =
            { tiname = t.name; titheory = t; tideps = getDepsFromTheory t }

        /// the main function exported from the module -
        /// takes a list of parsed theories and returns a structure
        // with all kinds of information that is needed
        let processTheories (ts:Theory list) : KnowledgeBase =
            { kbformalitems = getThmsDefsFromTheories ts; kbtheories = List.map getTheoryInfo ts }