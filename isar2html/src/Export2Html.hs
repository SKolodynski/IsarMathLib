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


module Export2Html
   where

import Data.List(isPrefixOf,intersperse)
import qualified Data.Map as M
import Data.Maybe(isJust, fromJust)

import IMLP_datatypes
import Utils
import IsarSym2Latex
import ProcessThys
import ExportCommon

-- | The function export2Html in this module takes a parsed
-- IsarMathLib theory and produces corresponding body of the HTML
-- document.

-- | converts literal latex: surround with "\( \)"
convLatex :: String -> String
convLatex s = "\\(" ++ s ++ "\\)"

-- | converts literal text: \<open> some text\<close>
littext :: [(String,String)] -> String -> String
littext repls s = if (isIdentifier s) then it s else (isar2latex repls s)

-- | make text italic
it :: String -> String
it s = "<i>" ++ s ++ "</i>"

-- | makes a string boldface, also surrounds with spaces
bf :: String -> String
bf s = "<b> " ++ s ++ " </b>"

-- | makes a paragraph
par :: String -> String
par s = if "<p>" `isPrefixOf` s then s
        else "<p>" ++ s ++ "</p>"

-- | makes a div to simulate paragraphs.
pd :: String -> String
pd s = "<div id=\"pardiv\" > " ++ s ++ "</div>"

-- | creates a heading
hd :: String -> String
hd s = "<h3>" ++ s ++ "</h3>"

-- | exports informal text
exp2inftext :: [(String,String)] -> String -> String
exp2inftext repls s = "<div class=\"inftext\">\n<p>" ++
   ( replace "\n\n" "</p>\n<p>" $
     appBetween convLatex "$" "$" $
     appBetween (littext repls) "\\<open>" "\\<close>" s ) ++
   "</p>\n</div>\n"

-- | creates a floating slider
floatSlider :: String -> String
floatSlider contents =
   "<span id=\"hintref\">" ++ contents ++ "</span>"

-- | creates a slider
slider :: String -> String -> String
slider tittle content = "<span id=\"hstrigger\" class=\"hideshow\" >" ++
   tittle ++ "</span>\n<div id=\"hscontent\" class=\"proof\" >" ++
   content ++ "\n</div>\n"

-- | creates a link
tlink :: String -> String -> String
tlink target text = "<a href=\"" ++ target ++"\">" ++ text ++ "</a>"

-- | creates an html option with a given name and value
hopt :: String -> String -> String
hopt nm val = nm ++ "=\"" ++ val ++"\" "

-- | makes an anchor for jumping inside page
anchor :: String -> String
anchor nm = "<a " ++ (hopt "name" nm) ++ "></a> "

-- | makes formal item with a given name
mkformal :: String -> String
mkformal s =
   "<div " ++
   (hopt "class" "formal") ++ ">" ++
   s ++ "\n</div>\n"

-- | renders a locale name in the theorem
inContext :: String -> String
inContext s =
   if (not $ null s) then "<b>(in</b> " ++ s ++ "<b>)</b> " else ""

-- | renders a reference hint that is displayed when a reference is clicked
refdiv :: String -> String -> String
refdiv id content = "<div id=\"" ++ id ++ "\"class=\"refhint\">" ++
   content ++ "</div>"

-- | exports a simplified form of a premise
exportPremiseSimple :: [(String,String)] -> PropPremise -> String
exportPremiseSimple repls (PropDefines defs) = 
    (bf "defines ") ++ (exportSimpleClaims repls defs) ++ "\n"
exportPremiseSimple repls (PropAssumes prms) =
    (bf "assumes ") ++ (exportSimpleClaims repls prms) ++ "\n"

-- | exports a list of premises in a simplified form
exportPremisesSimple ::  [(String,String)] -> [PropPremise] -> String
exportPremisesSimple repls pps = concatMap (par . exportPremiseSimple repls) pps

-- | exports FormalItemInfo
-- TODO start from here and rethink now we not only have assumes but defines as well
exportFormalItemInfo :: [(String,String)] -> FormalItemInfo -> String
exportFormalItemInfo repls (FormalItemInfo tn (SimpleProp tpe cntxt nme prms clms _)) =
   ( bf tpe) ++ " " ++
   ( inContext cntxt ) ++ (tlink (tn ++ ".html#"++ nme) nme) ++ ": " ++
   (exportPremisesSimple repls prms) ++
   ( bf " shows " ) ++ (exportSimpleClaims repls clms)

exportFormalItemInfo repls (FormalItemInfo tn ( SimpleDef nm d )) =
    ("Definition of " ++ nm ++ ":\n" ++ (isar2latex repls d) )


exportFormalItemInfo _ (FormalItemInfo tn OtherSimpleItem) = " Other formal item "

-- checks if a reference is on the list of known theorems and and if so creates
-- a div with the rendered simple form, otherwise returns an empty string
createRefDiv :: M.Map String String -> String -> String
createRefDiv mfii nm =
   if isJust lookres then refdiv nmAfterDot (fromJust lookres)
   else ""
     where
        nmAfterDot = reverse $ takeWhile (/='.') $ reverse nm
        lookres = (M.lookup nmAfterDot) mfii

-- | takes the template and the database of theorems and renders to html
exportTheories :: String -> KnowledgeBase -> [(String,String)]
exportTheories templ kb = map expThr tinfos where
   fi = kbformalitems kb
   repls = inner2LatexSym ++ (map def2replPair $ extractDefs fi)
   mfii = getRefsInfo repls fi
   tinfos = kbtheories kb
   tlinks = concatMap (thrylink . tiname) tinfos
   expThr tinfo = ("isarhtml/" ++ (tiname tinfo) ++ ".html", thHtml)
      where
         thHtml = replaceAll [ ("this is theory placeholder", exportedTheory)
                             , ("this is links placeholder", tlinks) ] templ
         exportedTheory = exportTheory repls mfii (tideps tinfo) (titheory tinfo)

-- | extracts definition names from knowledge base
extractDefs :: [FormalItemInfo] -> [String]
extractDefs = map (getName . fimitem) . filter isDefinition
    where
    getName (SimpleDef n _) = n

-- | makes a link to a rendered theory for the theory name
thrylink :: String -> String
thrylink thn =
   "\n<p><a href=\"" ++ thn ++ ".html\">" ++ thn ++ "</a></p>\n"

-- | converts Isar theory to HTML markup, the main function of this module
-- repls - a list of string replacements in formal code to convert it to LaTeX
-- mfii is a map of all known theorems rendered in simplified form,
-- refs - list of all references in all proofs of the theory
-- th - a parsed theory
exportTheory :: [(String,String)] -> M.Map String String -> [String] -> Theory -> String
exportTheory repls mfii refs th =
   uniquefyids ["hstrigger", "hscontent", "hintref","pardiv"] $
   ( mkformal $
   (bf "theory") ++ (name th) ++ (bf "imports") ++
   ( unwords $ imports th ) ) ++
   ( mkformal $ bf "begin\n" ) ++
   ( exp2inftext repls $ thIntro th ) ++
   ( unlines $ map (exportSubsection repls mfii) (thsections th) ) ++
   ( mkformal (bf "end\n") ) ++
   ( unlines $ map (createRefDiv mfii) refs )


-- | exports a section (same)
-- | repls - a list of replacements in LaTeX code
exportSubsection :: [(String,String)] -> M.Map String String -> Subsection ->  String
exportSubsection repls m s =
   ( hd $ sectitle s) ++ "\n" ++
   ( exp2inftext repls $ secIntro s) ++
   ( unlines $ map (exportItem repls m) $ items s )


-- | exports an item in a section (same)
exportItem :: [(String,String)] -> M.Map String String -> Item -> String
exportItem repls mfii it = ( exp2inftext repls $ description it ) ++ "\n" ++
                ( exportFormalItem repls mfii $ formalItem it )


-- | exports formal items
exportFormalItem :: [(String,String)] -> M.Map String String -> FormalItem -> String
exportFormalItem repls mfii (Abbreviation nm _ df) = mkformal $
    ( par $ (bf "Abbreviation") ) ++ (par $ isar2latex repls df)
exportFormalItem repls mfii (Definition id c _ _ df) = mkformal $
    ( par $ (bf "Definition")  ++ (if null c then "\n" else " (in " ++ c ++ ")") ) ++
    "\n" ++ (par $ isar2latex repls df )
exportFormalItem repls mfii (Locale nm (parent,vars) itms) = mkformal $
   ( par $ (bf "Locale ") ++ nm ++
      ( if null parent then "" else " = " ++ parent ++ " " ++ (unwords vars) ++ " +") ) ++
   (unlines $ map (exportLocaleItem repls) itms)
exportFormalItem repls mfii (FormalItem p) = exportProposition repls mfii p

-- | export locale item
exportLocaleItem :: [(String,String)] -> LocaleItem -> String
exportLocaleItem _ (Fixes nmnt) = ""

exportLocaleItem repls (Defines _ ld) =
   par $ ( bf "defines " ) ++ (isar2latex repls ld)

exportLocaleItem repls (Assumes clms ) =
   par $ ( bf "assumes " ) ++ (exportClaims repls clms)

-- | exports a single name with notation, as used in the "fixes"
-- locale item, just write the name, the notation is
-- evident from the "defines" line (same)
exportNameNotation :: [(String,String)] -> NameNotation -> String
exportNameNotation repls (NameNotation nm nt) = (isar2latex repls nm) ++ ", "

-- | exports a premise
exportPremise :: [(String,String)] -> PropPremise -> String
exportPremise repls (PropDefines defs) = par $ (bf "defines ") ++ (exportClaims repls defs)
exportPremise repls (PropAssumes prems) = par $ (bf "assumes ") ++ (exportClaims repls prems)

-- | exports proposition
exportProposition :: [(String,String)] -> M.Map String String -> Proposition -> String
exportProposition repls mfii p = anchor (propname p) ++ (mkformal $
   par ( ( bf $ proptype p ) ++ " " ++
   ( inContext $ context p) ++
   ( propname p ) ++ ":\n") ++
   ( concatMap (exportPremise repls) $  propprems p) ++
   ( bf "   shows " ) ++ ( exportClaims repls $ claims p ) ++
   ( exportProof repls mfii $ propproof p))

-- | exports a sequence of labelled claims (same)
exportClaims :: [(String,String)] -> [(String,[String])] -> String
exportClaims repls =  concat . (intersperse (bf "and ") ) . (map (exportOneClaim repls))

-- | exports a single labelled claim (same)
exportOneClaim :: [(String,String)] -> (String,[String]) -> String
exportOneClaim repls (label,claims) =
   label ++ (if null label then "" else ": ") ++
   ( concat $ append2Init ",  " $ map (isar2latex repls) claims )


-- | exports a proof
exportProof :: [(String,String)] -> M.Map String String -> Proof -> String
exportProof _ mfii ( UsingBy useunf uprops tac ) =
   if not $ null uprops then
      (bf useunf) ++ " " ++ (unwords $ intersperse ", " $ map (getRefSlider mfii) uprops )
   else " "


exportProof _ mfii (ByRule s) =
   (bf "  by (rule ") ++ (getRefSlider mfii s) ++ ( bf ")")

exportProof repls mfii (LongProof d ps) =
   slider "proof"
      ( rmdnl $ (unlines $ map (exportProofStep repls mfii) ps) ++ ( bf "qed" ) )

-- | exports a proof step
exportProofStep ::  [(String,String)] -> M.Map String String -> ProofStep -> String

exportProofStep repls mfii (LongReasoning rs mbs) =
   ( exportReasoning repls mfii rs ) ++ "\n" ++
   ( sunlines $ map (exportMoreoverBody repls mfii) mbs)

exportProofStep repls _ (FixStep v) = pd $
   (bf "fix ") ++ (unwords $ map (isar2latex repls) v)

exportProofStep repls _ (LetStep v d) = pd $
   (bf "let ") ++ ( isar2latex repls (v ++ " = " ++ d) )

exportProofStep _ _ Next = pd $ bf "next "


-- | exports a MoreoverBody (same)
exportMoreoverBody :: [(String,String)] -> M.Map String String -> MoreoverBody -> String
exportMoreoverBody repls mfii mb = pd $
   ( unlines $ map (prepKeyWord . (exportReasoning repls mfii)) (mrvMrvs mb) ) ++
   ( bf ultfinal ) ++ (exportProofCommand repls mfii (ultimfinal mb)) ++ "\n" ++
   ( sunlines $ map (exportConnectedStep repls mfii) (followup mb) )
   where
      s = mrvalso mb
      prepKeyWord = (((bf s) ++ " ") ++)
      ultfinal = if s == "also" then "finally " else "ultimately "


-- | exports a reasoning (same)
exportReasoning :: [(String,String)] -> M.Map String String -> Reasoning -> String
exportReasoning repls mfii (Reasoning is css ) =
    ( exportInitStep repls mfii is) ++ "\n" ++
        ( sunlines $ map (exportConnectedStep repls mfii) css )

-- | exports Init Step
exportInitStep :: [(String,String)] -> M.Map String String  -> InitStep -> String
exportInitStep repls mfii (InitStep loclabs pc) = pd $
   (if not $ null loclabs then
      ( exportLocRefs repls "from " loclabs )
   else "") ++
   (exportProofCommand repls mfii pc)

exportInitStep repls mfii (StepBlock pss) =
   ( slider "{" ( unlines $ map (exportProofStep repls mfii) pss ) ) ++
   ( bf "}" )

exportInitStep repls mfii (Assume clms) =
   pd $ (bf "assume " ) ++ exportClaims repls clms

exportInitStep repls mfii (Note refs) = pd $
   ( bf "note " ) ++ (unwords $ append2Init ", " $ map (exportLocRef repls) refs)

-- | exports init or connected proof local references
-- wft can be "with", "from", "then" (same)
exportLocRefs :: [(String,String)] -> String -> [String] -> String
exportLocRefs repls wft loclabs =
   (bf wft) ++ (concat $ append2Init ", " $ map (exportLocRef repls) loclabs) ++ " "


-- | export local reference. It may be a label or latex text in backquotes`
exportLocRef :: [(String,String)] -> String -> String
exportLocRef repls s = if (head s) == '`' then isar2latex repls $ tail $ init s
                 else s


-- | exports a connected step (like "with", "then" etc, those that
-- refere to the previous step
exportConnectedStep :: [(String,String)] -> M.Map String String -> ConnectedStep -> String
exportConnectedStep repls mfii (WithStep loclabs pc) = pd $
   ( exportLocRefs repls "with " loclabs ) ++ ( exportProofCommand repls mfii pc )

exportConnectedStep repls mfii ( ThenStep pc) = pd $
   (bf "then ") ++ ( exportProofCommand repls mfii pc)

exportConnectedStep repls mfii (HenceThus ht clms tac) = pd $
   (bf ht) ++ " " ++ (exportClaims repls clms)

-- | exports a proof command (same)
exportProofCommand :: [(String,String)] -> M.Map String String -> ProofCommand -> String
exportProofCommand repls mfii (PChaveShow hs cp) =
   (bf hs ) ++ " " ++ (exportClaimProof repls mfii cp)
exportProofCommand repls mfii (PCbtain vars cp) =
   (bf "obtain ") ++ (unwords $ map (isar2latex repls) vars) ++
   (bf "where ") ++ (exportClaimProof repls mfii cp)

-- | exports a claim with the proof (same)
exportClaimProof :: [(String,String)] -> M.Map String String -> ClaimProof -> String
exportClaimProof repls mfii cp =
   ( exportClaims repls (cpclaims cp) ) ++
   ( exportProof repls mfii (cpproof cp) )

-- | takes the map of formal items and a name of theorem,
-- returns a div that can be clicked on to show the hint
getRefSlider :: M.Map String String -> String -> String
getRefSlider mfii nm = if isJust lookres then
                          ( "<span id=\"hintref\">" ++ nmAfterDot ++ "</span>" )
                       else nm
                          where
                             nmAfterDot = reverse $ takeWhile (/='.') $ reverse nm
                             lookres = (M.lookup nmAfterDot) mfii


-- | create a lookup table of descriptions of referenced theorems
getRefsInfo :: [(String,String)] -> [FormalItemInfo] -> (M.Map String String)
getRefsInfo repls =  M.fromList . (map addKey)
   where addKey fii = (getSFIname $ fimitem fii, exportFormalItemInfo repls fii)

-- | exports a single simple (unlabelled) claim (same)
exportOneSimpleClaim :: [(String,String)] -> (String,[String]) -> String
exportOneSimpleClaim repls claims =
   unwords $ append2Init ",  " $ map (isar2latex repls) (snd claims)

-- | exports simple form of claims
exportSimpleClaims :: [(String,String)] -> [(String,[String])] -> String
exportSimpleClaims repls = concat . intersperse (bf " and " ). (map $ exportOneSimpleClaim repls)

isar2latex :: [(String,String)] -> String -> String
isar2latex repls s = remElems "`?" $ "\\( " ++
   (replace "\n" "\\)\n\\(" $ replaceAll repls $ convBraces s) ++ " \\)"

-- | makes unique every string occurence, adding the count as a div
-- at the end of the string
uniquefy :: String -> String -> String
uniquefy id htmlstring = st ++
   "<div id=\"par_" ++ id ++ "\" style=\" display: none\">" ++ (show count) ++ "</div>\n"
   where
      sti = foldr incrcount ("",0) htmlstring
      st = fst sti
      count = snd sti
      incrcount c (s,i) = 
         if id `isPrefixOf` ns then (id ++ (show i) ++ (drop (length id) ns), i+1)
         else (ns,i)
            where ns = c:s

-- composes some number of uniquefy fo a list of id strings
uniquefyids :: [String] -> String -> String
uniquefyids ids = foldr1 (.) (map uniquefy ids)


