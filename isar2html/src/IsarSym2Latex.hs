{-
	This file is part of isar2html - a tool for rendering IsarMathLib
	theories in in HTML.
    Copyright (C) 2008-2019  Slawomir Kolodynski

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
-}



module IsarSym2Latex
   where

import Utils(appBetween,appToParts,nestLevel)
import Data.Char(isAlpha)


-- | list of translations from Isar symbols to LaTeX symbols
-- inner2LatexSym :: [(String,String)]
inner2LatexSym = [("<", " \\lt ")
                 ,("%","\\%")
                 ,("\\<longrightarrow>", "\\longrightarrow ")
                 ,(".", ".\\ ")
                 ,(" O ", "\\circ ")
                 ,("\\<and>", "\\wedge ")
                 ,("\\<approx>", "\\approx ")
                 ,("\\<bar>","\\vert ")
                 ,("\\<bullet>", "\\bullet ")
                 ,("\\<ca>", " + ")
                 ,("\\<caddset>", " + ")
                 ,("\\<cmulset>", "\\cdot ")
                 ,("\\<circ>", "\\circ ")
                 ,("\\<cdiv>", " / ")
                 ,("\\<cltrrset>", "< ")
                 ,("\\<cn>", " - ")
                 ,("\\<cmnf>", "-\\infty ")
                 ,("\\<complex>", "\\mathbb{C} ")
                 ,("\\<cpnf>", "+\\infty ")
                 ,("\\<cs>", " - ")
                 ,("\\<delta>", "\\delta ")
                 ,("\\<epsilon>","\\varepsilon ")
                 ,("\\<eta>","\\eta ")
                 ,("\\<fd>", " / ")
                 ,("\\<fp>", " + ")
                 ,("\\<fm>", " - ")
                 ,("\\<gamma>", "\\gamma ")
                 ,("\\<Gamma>", "\\Gamma ")
                 ,("\\<i>", "\\imath ")
                 ,("max\\<delta>", "\\text{ max}\\delta " )
                 ,("\\<mulset>", "\\cdot ")
                 ,("\\<nat>", "\\mathbb{N} ")
                 ,("\\<subseteq>", "\\subseteq ")
                 ,("\\<times>", "\\times ")
                 ,("\\<rightarrow>", "\\rightarrow ")
                 ,("\\<langle>", "\\langle ")
                 ,("\\<Lambda>", "\\Lambda ")
                 ,("\\<lesssim>", "\\preceq ")
                 ,("\\<lsr>", "<_{\\mathbb{R}} ")
                 ,("\\<lsrset>", "<_{\\mathbb{R}} ")
                 ,("\\<rangle>", "\\rangle ")
                 ,("\\<cdot>", "\\cdot ")
                 ,("\\<degree>", "^\\circ ")
                 ,("\\<dots>", "\\ldots ")
                 ,("\\<equiv>", "\\equiv ")
                 ,("\\<hookleftarrow>", "\\hookleftarrow ")
                 ,("\\<int>", "\\mathbb{Z} ")
                 ,("\\<real>", "\\mathbb{R} ")
                 ,("\\<inter>", "\\cap ")
                 ,("\\<Inter>", "\\bigcap ")
                 ,("\\<lambda>", "\\lambda ")
                 ,("\\<le>", "\\leq ")
                 ,("\\<lfloor>", "\\lfloor ")
                 ,("\\<ls>", " < ")
                 ,("\\<lsq>", "\\leq ")
                 ,("\\<ltr>", " + ")
                 ,("\\<longleftrightarrow>", "\\longleftrightarrow ")
                 ,("\\<Longrightarrow>", "\\Longrightarrow ")
                 ,("\\<A>", "\\mathcal{A} ")
                 ,("\\<B>", "\\mathcal{B} ")
                 ,("\\<C>", "\\mathcal{C} ")
                 ,("\\<FF>", "\\mathfrak{F} ")
                 ,("\\<UU>", "\\mathfrak{U} ")
                 ,("\\<zero>", "0 ")
                 ,("\\<M>", "\\mathcal{M} ")
                 ,("\\<N>", "\\mathcal{N}")
                 ,("\\<S>", "\\mathcal{S} ")
                 ,("\\<T>", "\\mathcal{T} ")
                 ,("\\<X>", "\\mathcal{X} ")
                 ,("\\<ra>", " + ")
                 ,("\\<rm>", " - ")
                 ,("\\<not>","\\neg ")
                 ,("\\<noteq>", "\\neq ")
                 ,("\\<notin>", "\\notin ")
                 ,("\\<one>", "1 ")
                 ,("\\<oplus>","\\oplus ")
                 ,("\\<or>", "\\vee ")
                 ,("Orders", "\\text{ orders }")
                 ,("\\<partial>", "\\partial ")
                 ,("\\<phi>", "\\phi ")
                 ,("\\<Phi>", "\\Phi ")
                 ,("\\<pr>", "\\prod ")
                 ,("\\<psi>", "\\psi ")
                 ,("\\<prec>", "\\prec ")
                 ,("\\<Prod>", "\\prod ")
                 ,("\\<ra>", " + ")
                 ,("\\<rfloor>", "\\rfloor ")
                 ,("\\<rs>", " - ")
                 ,("\\<rm>", " - ")
                 ,("\\<rtr>", " + ")
                 ,("\\<rmu>", "\\cdot ")
                 ,("\\<sad>", " + ")
                 ,("\\<sdot>", "\\cdot ")
                 ,("\\<sigma>", "\\sigma ")
                 ,("\\<sim>", "\\sim ")
                 ,("\\<sm>", "-")
                 ,("\\<squnion>", "\\sqcup ")
                 ,("\\<sqinter>", "\\sqcap ")
                 ,("\\<Sum>", "\\sum ")
                 ,("\\<ssum>", "\\sum ")
                 ,("\\<tau>", "\\tau ")
                 ,("\\<three>", " 3 ")
                 ,("\\<two>", " 2 ")
                 ,("\\<four>", " 4 ")
                 ,("\\<five>", " 5 ")
                 ,("\\<six>", " 6 ")
                 ,("\\<seven>", " 7 ")
                 ,("\\<eight>", " 8 ")
                 ,("\\<nine>", " 9 ")
                 ,("\\<zero>", " 0 ")
                 ,("\\<twosuperior>","^2 ")
                 ,("\\<union>", "\\cup ")
                 ,("\\<Union>", "\\bigcup ")
                 ,("\\<forall>", "\\forall ")
                 ,("\\<exists>", "\\exists ")
                 ,("\\<in>", "\\in ")
                 ,("#", "\\ \\sharp ")
                 ,("isASet","\\text{ is a set }")
                 ,("THE", "\\text{The }")
                 ,("Xor", "\\text{ Xor } ")
                 ,("antisym(","\\text{antisym}(")
                 ,("bij(","\\text{bij}(")
                 ,(" directs ","\\text{ directs }")
                 ,("Exactly\\_1\\_of\\_3\\_holds","\\text{Exactly_1_of_3_holds} ")
                 ,("equiv(","\\text{equiv}(")
                 ,("fst(","\\text{fst}(")
                 ,("Card(","\\text{Card}(")
                 ,("CoCardinal(","\\text{CoCardinal}(")
                 ,("csucc(","\\text{csucc}(")
                 ,("default","\\text{default}")
                 ,("ExcludedSet(","\\text{ExcludedSet}(")
                 ,("HasAnInfimum(","\\text{HasAnInfimum}(")
                 ,("if ","\\text{if }")
                 ,("IncludedSet(","\\text{IncludedSet}(")
                 ,("InfCard(","\\text{InfCard}(")
                 ,("inj(","\\text{inj}(")
                 ,("range(","\\text{range}(")
                 ,("restrict(","\\text{restrict}(")
                 ,("roelckeUniformity","\\text{roelckeUniformity}")
                 ,("Pi(","\\text{Pi}(")
                 ,("snd(","\\text{snd}(")
                 ,("surj(","\\text{surj}(")
                 ,(" then ","\\text{ then }")
                 ,(" else ","\\text{ else }")
                 ,("leftUniformity","\\text{ leftUniformity }")
                 ,("rightUniformity","\\text{ rightUniformity }")
                 ,("trans(","\\text{trans}(")
                 ,("Neigh","\\text{Neigh}")
                 ,("Net(","\\text{Net}(")
                 ,("natify(","\\text{natify}(")
                 ,("refl(","\\text{refl}(")
                 ,("inf ","\\text{inf}")
                 ,("sup ","\\text{sup}")
                 ,(" zdiv ", "\\text{ zdiv }")
                 ,(" zmod ", "\\text{ zmod }")
                 ,("\\<zmu>", "\\cdot ")
                 ,("\\<za>", " + ")
                 ,("\\<zlq>", "\\leq ")
                 ,("\\<zm>", " - ")
                 ,("\\<zs>", " - ")
                 ,("\\<^isub>", "_")
                 ,("\\<^isup>", "^")
                 ,("\\<^sub>", "_")
                 ,("\\<^sup>", "^")
                 ,("_", "\\_")
                 ,("-``", "^{-1}")
                 ,("$", "\\ \\$ ")
                 ,(" \\{in\\} ","\\text{ in }")
                 ,(" \\{and\\}","\\text{ and }")
                 ,("\\<inverse>", "^{-1}")
                 ,("\\<sinv>", "^{-1}")
                 ]


convBraces :: String -> String
convBraces = fst . unzip . (convTextsLevel (0::Int)) . (nestLevel '{' '}')

-- | returns true if a character is not a letter or space
isNotAlphaSpaceBrace :: (Char, Int) -> Bool
isNotAlphaSpaceBrace (c,n) = not $ (isAlpha c || c==' ' || c=='{' || c=='}')

-- | takes a list of (character, nest level) pairs and decides
-- if this represents a set comprehension. Set comprehensions are
-- those that have a dot on this nest level
isSetCompr :: Int -> [(Char,Int)] -> Bool
isSetCompr lev s = (length s < 11) || (any isNotAlphaSpaceBrace s )
   -- (any ( \(c,n) -> (c == '.' &&  n == (lev+1) ) ) s)

-- | converts a string zipped with nesting level information
-- convTextsNestLev :: [(Char,Int)] -> [(Char,Int)]
-- convTextsNestLev

convTextsLevel :: Int -> [(Char,Int)] -> [(Char,Int)]
convTextsLevel n = appToParts ((> n) . snd) (convSetComprPred  n)

-- | converts a string representing a set comprehension
-- or a predicate starting from given nest level
-- assumes that the input starts with ('{',n) and ends with ('}',n)

convSetComprPred :: Int -> [(Char,Int)] -> [(Char,Int)]
convSetComprPred n sp = if isSetCompr n sp then convSetCompr n sp
                      else convPredicate n sp

-- | converts a set comprehension with nest level information
convSetCompr :: Int -> [(Char,Int)] -> [(Char,Int)]
convSetCompr n sp =
   [( '\\', n), ( '{', n)] ++
   (tail $ init $ convTextsLevel (n+1)sp) ++
   [( '\\', n), ( '}', n)]

-- | converts a predicate
convPredicate n sp =
   ( zip "\\text{ " (replicate 7 n) ) ++
   (tail $ init sp) ++
   [( ' ',n),( '}', n)]

-- | converts a definition name to a pair that can be used for replacements
def2replPair :: String -> (String,String)
def2replPair s = (s++['(']," \\text{" ++ s ++ "}(")
