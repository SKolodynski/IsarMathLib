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

    module IsarSym2Latex =
        open Utils
        open System

        /// a macro that expands the binomial
        let macroBinom (args:string array) :string =
            "{{"+args[0]+"}\\choose {"+args[1]+"}}"

        /// expands powers: pow(n,x) --> x^n Note the reversed order of the parameters
        let macroPow (args:string array) :string =
            if args[1].Length = 1 then args[1]+"^{"+args[0]+"}"
            else "("+args[1]+")"+"^{"+args[0]+"}"


        /// list of macros to be expanded, the first string is macro name, 
        /// the second is the template
        let macros : (string*((string array -> string))) array = 
            [| "Binom", macroBinom;
                "pow",macroPow|]

        /// list of translations from Isar symbols to LaTeX symbols
        // TODO: read from a file maybe?
        let inner2LatexSym : (string*string) list =
                [("<", " \\lt ")
                 ("%","\\%")
                 ("\\<longrightarrow>", "\\longrightarrow ")
                 (".", ".\\ ")
                 (" O ", "\\circ ")
                 ("\\<ad>", " + ")
                 ("\\<and>", "\\wedge ")
                 ("\\<approx>", "\\approx ")
                 ("\\<bar>","\\vert ")
                 ("\\<bullet>", "\\bullet ")
                 ("\\<ca>", " + ")
                 ("\\<caddset>", " + ")
                 ("\\<cmulset>", "\\cdot ")
                 ("\\<circ>", "\\circ ")
                 ("\\<cdiv>", " / ")
                 ("\\<cltrrset>", "< ")
                 ("\\<cn>", " - ")
                 ("\\<cmnf>", "-\\infty ")
                 ("\\<complex>", "\\mathbb{C} ")
                 ("\\<cpnf>", "+\\infty ")
                 ("\\<cs>", " - ")
                 ("\\<delta>", "\\delta ")
                 ("\\<epsilon>","\\varepsilon ")
                 ("\\<eta>","\\eta ")
                 ("\\<fd>", " / ")
                 ("\\<fp>", " + ")
                 ("\\<fm>", " - ")
                 ("\\<triangleleft>", "\\triangleleft ")
                 ("\\<gamma>", "\\gamma ")
                 ("\\<Gamma>", "\\Gamma ")
                 ("\\<i>", "\\imath ")
                 ("max\\<delta>", "\\text{ max}\\delta " )
                 ("\\<mulset>", "\\cdot ")
                 ("\\<nat>", "\\mathbb{N} ")
                 ("\\<subseteq>", "\\subseteq ")
                 ("\\<times>", "\\times ")
                 ("\\<rightarrow>", "\\rightarrow ")
                 ("\\<langle>", "\\langle ")
                 ("\\<Lambda>", "\\Lambda ")
                 ("\\<lesssim>", "\\preceq ")
                 ("\\<lsr>", "<_{\\mathbb{R}} ")
                 ("\\<lsrset>", "<_{\\mathbb{R}} ")
                 ("\\<rangle>", "\\rangle ")
                 ("\\<cdot>", "\\cdot ")
                 ("\\<degree>", "^\\circ ")
                 ("\\<dots>", "\\ldots ")
                 ("\\<equiv>", "\\equiv ")
                 ("\\<hookleftarrow>", "\\hookleftarrow ")
                 ("\\<int>", "\\mathbb{Z} ")
                 ("\\<real>", "\\mathbb{R} ")
                 ("\\<inter>", "\\cap ")
                 ("\\<Inter>", "\\bigcap ")
                 ("\\<lambda>", "\\lambda ")
                 ("\\<le>", "\\leq ")
                 ("\\<ld>", "\\backslash ")
                 ("\\<lfloor>", "\\lfloor ")
                 ("\\<ls>", " < ")
                 ("\\<lsq>", "\\leq ")
                 ("\\<ltr>", " + ")
                 ("\\<nm>", "\\cdot ")
                 ("\\<longleftrightarrow>", "\\longleftrightarrow ")
                 ("\\<Longrightarrow>", "\\Longrightarrow ")
                 ("\\<A>", "\\mathcal{A} ")
                 ("\\<B>", "\\mathcal{B} ")
                 ("\\<C>", "\\mathcal{C} ")
                 ("\\<F>", "\\mathcal{F} ")
                 ("\\<I>", "\\mathcal{I} ")
                 ("\\<J>", "\\mathcal{J} ")
                 ("\\<R>", "\\mathcal{R} ")
                 ("\\<FF>", "\\mathfrak{F} ")
                 ("\\<UU>", "\\mathfrak{U} ")
                 ("\\<ff>", "\\mathfrak{f} ")
                 ("\\<zero>", "0 ")
                 ("\\<D>", "\\mathcal{D} ")
                 ("\\<M>", "\\mathcal{M} ")
                 ("\\<N>", "\\mathcal{N}")
                 ("\\<P>", "\\mathcal{P}")                 
                 ("\\<S>", "\\mathcal{S} ")
                 ("\\<T>", "\\mathcal{T} ")
                 ("\\<X>", "\\mathcal{X} ")
                 ("\\<ra>", " + ")
                 ("\\<rd>", "/ ")
                 ("\\<rm>", " - ")
                 ("\\<not>","\\neg ")
                 ("\\<noteq>", "\\neq ")
                 ("\\<notin>", "\\notin ")
                 ("\\<one>", "1 ")
                 ("\\<oplus>","\\oplus ")
                 ("\\<or>", "\\vee ")
                 ("Orders", "\\text{ orders }")
                 ("\\<partial>", "\\partial ")
                 ("\\<phi>", "\\phi ")
                 ("\\<Phi>", "\\Phi ")
                 ("\\<Theta>", "\\Theta ")
                 ("\\<pr>", "\\prod ")
                 ("\\<psi>", "\\psi ")
                 ("\\<prec>", "\\prec ")
                 ("\\<Prod>", "\\prod ")
                 ("\\<ra>", " + ")
                 ("\\<rfloor>", "\\rfloor ")
                 ("\\<rs>", " - ")
                 ("\\<rm>", " - ")
                 ("\\<rtr>", " + ")
                 ("\\<rmu>", "\\cdot ")
                 ("\\<sad>", " + ")
                 ("\\<sdot>", "\\cdot ")
                 ("\\<sigma>", "\\sigma ")
                 ("\\<sim>", "\\sim ")
                 ("\\<sm>", "-")
                 ("\\<squnion>", "\\sqcup ")
                 ("\\<sqinter>", "\\sqcap ")
                 ("\\<Sum>", "\\sum ")
                 ("\\<ssum>", "\\sum ")
                 ("\\<tau>", "\\tau ")
                 ("\\<three>", " 3 ")
                 ("\\<two>", " 2 ")
                 ("\\<four>", " 4 ")
                 ("\\<five>", " 5 ")
                 ("\\<six>", " 6 ")
                 ("\\<seven>", " 7 ")
                 ("\\<eight>", " 8 ")
                 ("\\<nine>", " 9 ")
                 ("\\<zero>", " 0 ")
                 ("\\<twosuperior>","^2 ")
                 ("\\<union>", "\\cup ")
                 ("\\<Union>", "\\bigcup ")
                 ("\\<forall>", "\\forall ")
                 ("\\<exists>", "\\exists ")
                 ("\\<in>", "\\in ")
                 //("#", "\\ \\sharp ")
                //  (" #+ ", " +_\\mathbb{N} ")
                //  (" #- ", " -_\\mathbb{N} ")
                //  (" #* ", " \\cdot_\\mathbb{N} ")
                 (" #+ ", " + ")
                 (" #- ", " - ")
                 (" #* ", " \\cdot ")
                 ("isASet","\\text{ is a set }")
                 ("THE", "\\text{The }")
                 ("Xor", "\\text{ Xor } ")
                 ("antisym(","\\text{antisym}(")
                 ("bij(","\\text{bij}(")
                 (" directs ","\\text{ directs }")
                 ("Exactly\\_1\\_of\\_3\\_holds","\\text{Exactly_1_of_3_holds} ")
                 ("equiv(","\\text{equiv}(")
                 ("fst(","\\text{fst}(")
                 ("Card(","\\text{Card}(")
                 ("CoCardinal(","\\text{CoCardinal}(")
                 ("csucc(","\\text{csucc}(")
                 ("default","\\text{default}")
                 ("ExcludedSet(","\\text{ExcludedSet}(")
                 ("HasAnInfimum(","\\text{HasAnInfimum}(")
                 ("HasLeftDiv(","\\text{HasLeftDiv}(")
                 ("HasRightDiv(","\\text{HasRightDiv}(")
                 ("IsAquasigroup(","\\text{IsAquasigroup}(")
                 ("if ","\\text{if }")
                 ("IncludedSet(","\\text{IncludedSet}(")
                 ("InfCard(","\\text{InfCard}(")
                 ("InEnd(","\\text{InEnd}(")
                 ("inj(","\\text{inj}(")
                 ("\\{is T_0\\}","\\text{ is }T_0")
                 ("\\{is T_1\\}","\\text{ is }T_1")
                 ("\\{is T_2\\}","\\text{ is }T_2")
                 ("\\{up-directs\\}","\\text{ up-directs }")
                 ("\\{down-directs\\}","\\text{ down-directs }")
                 ("range(","\\text{range}(")
                 ("restrict(","\\text{restrict}(")
                 ("roelckeUniformity","\\text{roelckeUniformity}")
                 ("Pi(","\\text{Pi}(")
                 ("snd(","\\text{snd}(")
                 ("surj(","\\text{surj}(")
                 (" then ","\\text{ then }")
                 (" else ","\\text{ else }")
                 ("leftUniformity","\\text{ leftUniformity }")
                 ("rightUniformity","\\text{ rightUniformity }")
                 ("LeftDiv(","\\text{ LeftDiv}(")
                 ("RightDiv(","\\text{ RightDiv}(")
                 ("trans(","\\text{trans}(")
                 ("TheNeutralElement(","\\text{ TheNeutralElement}(")
                 ("Neigh","\\text{Neigh}")
                 ("Net(","\\text{Net}(")
                 ("natify(","\\text{natify}(")
                 ("refl(","\\text{refl}(")
                 ("inf ","\\text{inf}")
                 ("sup ","\\text{sup}")
                 (" zdiv ", "\\text{ zdiv }")
                 (" zmod ", "\\text{ zmod }")
                 ("\\<zmu>", "\\cdot ")
                 ("\\<za>", " + ")
                 ("\\<zlq>", "\\leq ")
                 ("\\<zm>", " - ")
                 ("\\<zs>", " - ")
                 ("\\<^isub>", "_")
                 ("\\<^isup>", "^")
                 ("\\<^sub>", "_")
                 ("\\<^sup>", "^")
                 ("_", "\\_")
                 ("-``", "^{-1}")
                 ("$", "\\ \\$ ")
                 (" \\{and\\}","\\text{ and }")
                 (" \\{by\\}","\\text{ by }")
                 (" \\{from\\}","\\text{ from }")
                 (" \\{in\\} ","\\text{ in }")
                 ("\\<inverse>", "^{-1}")
                 ("\\<sinv>", "^{-1}")
                 ]
        
        
        /// converts a predicate like "{is a topology}"
        let convPredicate (n:int) (sp:(char*int) list) : (char*int) list =
            (Seq.zip "\\text{ " (Seq.replicate 7 n)) 
            |> thenAppend (dropEnds sp) 
            |> thenAppend (seq {(' ', n); ('}', n)})
            |> Seq.toList

        /// returns true if a character is not a letter or space or curly brace
        let isNotAlphaSpaceBrace (c:char,n:int) : bool = 
            not (Char.IsLetter c || c=' ' || c='{' || c='}')

        /// takes a list of (character, nest level) pairs and decides
        /// if this represents a set comprehension. Set comprehensions 
        /// are heuristically recognized as having length less than 11
        /// or characters that are not letters, spaces of braces.
        /// TODO: this is a crappy way, try to find a better one.
        let isSetCompr (s:(char*int) list) : bool =
            s.Length<11 || (any isNotAlphaSpaceBrace s)

        /// converts a string with level info representing a set comprehension
        ///  or a predicate starting from given nest level
        /// assumes that the input starts with ('{',n) and ends with ('}',n)
        // TODO: add spaces after \{ and \}, it's LaTeX safer this way
        let rec convTextsLevel n  =
            appToParts (snd >> (<) n) (convSetComprPred n) // ((<) n) x evaluates to  n < x 
        and convSetComprPred (n:int) (sp:(char*int) list) : (char*int) list =
             if isSetCompr sp then convSetCompr n sp else convPredicate n sp
        and convSetCompr n sp =
            seq [('\\',n);('{',n)]
            |> thenAppend (convTextsLevel (n+1) sp |> dropEnds)
            |> thenAppend (seq [('\\',n);( '}', n)])
            |> Seq.toList
       
        /// converts expressions of the form "{...}" in the inner logic. 
        /// This might be a set comprehension, a singleton or a predicate like "{is a topology}"
        /// with similar expressions inside that need to be converted as well
        let convBraces : string -> string =
            nestLevel '{' '}' >> convTextsLevel 0 >> List.unzip 
            >> fst >> List.map string >> List.reduce (+)
        
        /// converts a definition name to a pair that can be used for replacements
        let def2replPair (s:string) : string*string = (s+"("," \\text{" + s + "}(")

        
        
