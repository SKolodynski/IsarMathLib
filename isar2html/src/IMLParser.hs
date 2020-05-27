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


module IMLParser
   where

import Text.ParserCombinators.Parsec
import IMLP_datatypes
import Utils

keywords = [ "have", "show", "obtain", "where", "proof"
           , "ultimately", "finally", "for", "assume", "let", "then"
           , "moreover", "also", "from", "defines", "fixes"
           , "note"]

-- parses nonempty text that does not contain any of the strings in the parameter and does not start with the backslash
-- consumes the text until one of the given strings, not including
pureText :: [String]-> Parser String
pureText ss = do
    notFollowedBy (choice (map (try . string) ss))
    manyTill anyChar (choice (map (lookAhead . try . string) ss))


-- like textBetween, but returns the enclosing delimiters
enclosedIn :: String -> String -> Parser String
enclosedIn start end = do
    string start
    t <- manyTill anyChar (try (string end))
    return (start ++ t ++ end)

-- like textBetween, but ignores the sections inside
-- parseTest (betweenNest "\\<open>" "\\<close>") "\\<open> sksks \\<open>enclosed \\<close> \\<close> abc"
-- " sksks \\<open>enclosed \\<close> "
-- the regular (textBetween "\\<open>" "\\<close>") would stop in the first "\\<close>" tah and return
-- " sksks \\<open>enclosed "
betweenNest :: String -> String -> Parser String
betweenNest start end = do
    string start
    txts <- many1 ((pureText [start,end]) <|> (try (enclosedIn start end)))
    string end
    return (concat txts)

-- | parses and returns any text between start and end.
textBetween :: String -> String -> Parser String
textBetween start end = do
   string start
   t <- manyTill anyChar (try (string end))
   return t

-- | parses and returns Isar comments
comment :: Parser String
comment = "(*" `textBetween` "*)"

-- | parses and returns the informal text (the text between
-- "text\<open>" and "\<close>"
informalText :: Parser String
informalText = do
    string "text"
    spaces
    "\\<open>" `betweenNest` "\\<close>"

-- | parses the section line, returns the section title.
section :: Parser String
section = do
    string "section"
    spaces
    "\\<open>" `textBetween` "\\<close>"

-- | this parses a word that consists of alphanumeric characters
-- plus a list of some additional allowed characters given in the
-- argument, but fails if that word is any of the keywords
alphaNumNotKeyword :: String -> Parser String
alphaNumNotKeyword chars = do
   notAnyOf $ map (try . string) keywords
   many1 (alphaNum <|> (choice $ map char chars))

-- | parses a valid theory or proposition name, also labels.
itemName :: Parser String
itemName = alphaNumNotKeyword "_.,()"

-- | like an the itemName, but we don't allow parantheses
pureItemName :: Parser String
pureItemName = alphaNumNotKeyword "_."


-- | parses a variable name
varname :: Parser String
varname = alphaNumNotKeyword "_\\<>^"

-- | parses a quote reference. Isabelle 2007 allows to
-- refere by writing a fact, like `a \<in>B` instead of A1
literalQuote :: Parser String
literalQuote = do
   q <- textBetween "\\<open>" "\\<close>"
   return ("`" ++ q ++ "`")

-- | parses label reference name. Labels references
-- in Isabelle 2007 can be either like item names or
labelRef :: Parser String
labelRef = itemName <|> literalQuote

notAnyOf :: [Parser tok] -> Parser ()
notAnyOf words = try ( do { try (choice words)
                          ; unexpected ""}
                      <|> return () )


-- | parses inner text (the stuff between "")
innerText :: Parser String
innerText = ("\"" `textBetween` "\"") <|> string "?thesis"

-- | parses a preamble of definition, smth. like
-- IsATopology ("_ {is a topology}" [90] 91) where
-- IsASet :: "i\<Rightarrow>o" ("_ isASet" [90] 90) where
-- IsComplete ("_ {is complete}") where
defpreamble :: Parser (String, String, String, String)
defpreamble = do
   c <- option "" incontext
   spaces
   name <- itemName
   spaces
   ts <- option "" typespec
   spaces
   spec <- option "" defnotation
   spaces
   string "where"
   return (name, c, ts,spec)

-- | parses definition notation like
-- (infixl "Xor" 66)
-- NetOfFilter ("Net(_)" 40)
-- ("_ {is complete}")
defnotation :: Parser String
defnotation = do
    char '('
    fixity <- option "" (many1 letter)
    spaces
    notation <- textBetween "\"" "\""
    spaces
    assocL <- option "" (textBetween "[" "]")
    spaces
    assoc <- option "" (many1 digit)
    spaces
    char ')'
    return ("(" ++ fixity ++ " \"" ++ notation ++ "\" " ++
            "[" ++ assocL ++ "]" ++ assoc ++ ")")


-- | parses a type specification like
-- :: "i\<Rightarrow>o")
-- This is very rarely needed as Isabelle does type inference.
typespec :: Parser String
typespec = do
 string ":: "
 s <- textBetween "\"" "\""
 return s

-- | parses an assertion label with a possible "simp" modifier.
-- The parser returns a string which is the label and True if the simp was present or False if not
labelsimp :: Parser (String, Bool)
labelsimp = do
   dn <- varname
   spaces
   s <- option "" (string "[simp]")
   char ':'
   return (dn, s /= "")

-- | parses abbreviations
abbreviation :: Parser FormalItem
abbreviation = do
    string "abbreviation"
    spaces
    nm <- pureItemName
    nt <- textBetween "(\"" "\")"
    spaces
    string "where"
    spaces
    d <- innerText
    return Abbreviation
        { abbname = nm
        , abbnotation = nt
        , abbspec = d
        }

-- | parses definitions. Note we require a space before \<equiv> in the definition
definition :: Parser FormalItem
definition = do
   string "definition"
   spaces
   (name,contxt,tspec,spec) <- option ("","","","") defpreamble
   spaces
   ls <- option ("", False) labelsimp
   spaces
   d <- innerText
   return Definition
      { defname = if (name /= "") then name else extrName d
      , defcontext = contxt
      , deftypespec = spec
      , deflabel = ls
      , def = d }
   where extrName = takeWhile (/= '(') . takeWhile (/= ' ')

-- | parses locale
locale :: Parser FormalItem
locale = do
   string "locale"
   spaces
   n <- itemName
   spaces
   char '='
   spaces
   inhf <- option ("",[]) ( do
                            parent <- itemName
                            spaces
                            vars <- option [] renamedvars
                            spaces
                            char '+'
                            spaces
                            return (parent,vars) )
   li <- localeItem `sepEndBy1` spaces
   return (Locale { localename = n
                  , inheritsFrom = inhf
                  , localeItems = li })

-- parses a list of variables with a "for clause" that appeared in Isabelle 2009.
-- looks like "K A M for K A M". This is the only for we support in the parser,
-- a list of variables, then "for", then another list of variables that we ignore
renamedvars :: Parser [String]
renamedvars = do
   vars <- (varname `sepEndBy1` spaces)
   string "for"
   spaces
   varname `sepEndBy1` spaces
   return vars

-- | parses a locale item: "fixes", "defines" or "assumes"
localeItem :: Parser LocaleItem
localeItem = locItemfixes <|> locItemDefines <|> locItemAssumes <?>
   "expected a \"fixes\", \"defines\" or \"assumes\" locate item."

-- | parses a "fixes" locale item
locItemfixes :: Parser LocaleItem
locItemfixes = do
   string "fixes"
   spaces
   nmnt <- namenotation `sepEndBy1` spaces
   return (Fixes nmnt)

-- parses a variable name with its notation
namenotation :: Parser NameNotation
namenotation = do
   iname <- varname
   spaces
   notation <- ("(" `textBetween` ")") <|> return ""
   return NameNotation {fixedName = iname, fixedNotation = notation}

-- | parses a "defines" locale item
locItemDefines :: Parser LocaleItem
locItemDefines = do
   string "defines"
   spaces
   ls <- labelsimp
   spaces
   ld <- "\"" `textBetween` "\""
   return ( Defines { locdefNameSimp = ls, locdef = ld } )

-- | parses an "assumes" locale item
locItemAssumes :: Parser LocaleItem
locItemAssumes = do
   string "assumes"
   spaces
   a <- listLabStatLists
   return (Assumes a )

-- | parses a Subsection
subsection :: Parser Subsection
subsection = do
   st <- "subsection\\<open>" `textBetween` "\\<close>"
   spaces
   si <- informalText
   spaces
   --its <- itemWdescription `sepEndBy1` spaces
   its <- itemWdescription `sepEndBy` spaces
   return Subsection { sectitle = st, secIntro = si, items = its }

-- | parses formal item with its description
itemWdescription :: Parser Item
itemWdescription = do
   desc <- informalText
   spaces
   fitem <- abbreviation <|> definition <|> try locale <|> proposition -- (l)ocale like (l)emma
   return ( Item { description = desc, formalItem = fitem } )

-- | parses a theory
theoryParser :: Parser Theory
theoryParser = do
   --lic      <- comment
   spaces
   s        <- section
   spaces
   string "theory"
   char ' '
   n        <- itemName
   char ' '
   string "imports "
   importlist <- itemName `sepBy1` (char ' ')
   spaces
   string "begin"
   spaces
   i <- informalText
   spaces
   ss <- subsection `sepEndBy1` spaces
   string "end"
   return (Theory { header  = s
                  , name    = n
                  , imports = importlist
                  , thIntro = i
                  , thsections = ss} )

theoryTest :: Parser Theory
theoryTest = do
   --lic      <- comment
   spaces
   s        <- section
   spaces
   string "theory"
   char ' '
   n        <- itemName
   char ' '
   string "imports "
   importlist <- itemName `sepBy1` (char ' ')
   spaces
   string "begin"
   spaces
   i <- informalText
   spaces
   ss <- subsection `sepEndBy1` spaces
   string "end"
   return (Theory { header  = s
                  , name    = n
                  , imports = importlist
                  , thIntro = ""
                  , thsections = []} )

-- parses a locale name in a proposition
incontext :: Parser String
incontext = textBetween "(in "  ")"

-- | parses a proposition
proposition :: Parser FormalItem
proposition = do
   t <- string "theorem" <|> string "lemma" <|> string "corollary"
   char ' '
   c <- option "" incontext
   spaces
   n <- itemName
   char ':'
   spaces
   p <- ( premises <|> return [] )
   string "shows"
   cl <- listLabStatLists
   spaces
   pr <- proof
   return (FormalItem Proposition
                      {proptype = t
                      , context = c
                      , propname = n
                      , propprems = p
                      , claims = cl
                      , propproof = pr } )


-- | parses "assumes" and "defines" statements in the premises
-- of a proposition
premises :: Parser [PropPremise]
-- premises = many (premassumes <|> premdefines)
premises = (premassumes <|> premdefines) `sepEndBy` spaces

-- | parses an "assumes" statement
premassumes :: Parser PropPremise
premassumes = do
   string "assumes"
   spaces
   p <- listLabStatLists
   return (PropAssumes p)

premdefines :: Parser PropPremise
premdefines = do
    string "defines"
    spaces
    p <- listLabStatLists
    return (PropDefines p)

-- | parses labelled statement list
-- like A1: "a \<in> A"  "b \<in> B"
labelledStatList :: Parser (String,[String])
labelledStatList = do
   label <- statLabel <|> return ""
   spaces
   inners <- innerText `sepEndBy1` spaces
   return (label, inners)

-- | parses a list of labelled statement lists
listLabStatLists :: Parser [(String,[String])]
listLabStatLists = labelledStatList `sepBy1` (spaces >> (try $ string "and") >> spaces)


-- | parses a statement label
statLabel :: Parser String
statLabel = do
   n <- itemName
   char ':'
   return n

-- | parses short proof that has only a tactic in it
shortProofByTac :: Parser Proof
shortProofByTac = do
   string "by"
   spaces
   tac <- tactic
   return ( UsingBy { useunfold = "", usedprops = [], ptactic = tac } )

-- | parses short proof that has "using" or "unfolding" keyword with references
shortProofRefTac :: String -> Parser Proof
shortProofRefTac meth = do
   string meth
   spaces
   itms <- (manyTill (do {i <- itemName; spaces; return i}) (try (string "by")))
   spaces
   tac <- tactic
   return ( UsingBy { useunfold = meth, usedprops = itms, ptactic = tac } )

-- parsers a tactic
tactic :: Parser String
--tactic = choice $ map string ["simp", "auto", "blast", "fast"]
tactic = string "simp" <|> string "auto" <|> string "blast" <|>
        try (string "fast") <|> string "force"

-- parses "by rule(... )" type of proof
shortProofByRule :: Parser Proof
shortProofByRule = do
   string "by (rule "
   r <- pureItemName
   char ')'
   return (ByRule r)

-- | parses an item with space
itemSpace :: Parser String
itemSpace = do
   i <- itemName
   spaces
   return i

-- | parses obtain ... where... with proof
proofcomobtain :: Parser ProofCommand
proofcomobtain = do
   string "obtain"
   spaces
   vars <- varname `sepEndBy` spaces
   string "where"
   spaces
   cp <- claimproof
   return ( PCbtain vars cp )

-- | parses have with proof or show with proof
proofcomhaveshow :: Parser ProofCommand
proofcomhaveshow = do
   hs <- string "have" <|> string "show"
   spaces
   cp <- claimproof
   return $ PChaveShow hs cp

-- | parses a proof command - have, show or obtain
proofcom :: Parser ProofCommand
proofcom = proofcomobtain <|> proofcomhaveshow

-- | parses a False constant. This is treated as a kind of claim
claimfalse :: Parser [(String,[String])]
claimfalse = do
   string "False"
   return [("",["False"])]

-- | parses a claim with a proof
claimproof :: Parser ClaimProof
claimproof = do
   c <- (try listLabStatLists) <|> claimfalse
   spaces
   p <- proof
   return ClaimProof { cpclaims = c, cpproof = p }

-- | parses assume ...
assume :: Parser InitStep
assume = do
   string "assume"
   spaces
   a <- listLabStatLists
   return (Assume a)

-- | parses "note"
note :: Parser InitStep
note = do
   ss <- locrefs "note"
   return (Note ss)

-- | parses a proof block (is this OK with nested blocks?)
stepblock :: Parser InitStep
stepblock = do
   char '{'
   spaces
   ps <- proofstep `sepEndBy1` spaces
   char '}'
   return (StepBlock ps)

-- | parses an initit statement in a resoning.
-- We have to try "note", because it otherwise it may consume
initStep :: Parser InitStep
initStep = stepblock <|> assume <|> note <|>
  ( do
       lr <- option [] (locrefs "from")
       spaces
       pc <- proofcom
       return (InitStep lr pc)
       )

-- Parses "then" type of connected step
thenstep :: Parser ConnectedStep
thenstep = do
   string "then"
   spaces
   pc <- proofcom
   return (ThenStep pc)

-- Parses "hence" or "thus" type of connected step
hencethus :: Parser ConnectedStep
hencethus = do
   ht <- string "hence" <|> string "thus"
   spaces
   c <- (try listLabStatLists) <|> claimfalse
   spaces
   string "by"
   char ' '
   tac <- tactic
   return $ HenceThus { henceorthus = ht
                    , ttclaims = c
                    , tttactic = tac }

-- | Parse "with" type of connected step
withstep :: Parser ConnectedStep
withstep = do
   lr <- locrefs "with"
   spaces
   pc <- proofcom
   return ( WithStep lr pc )

-- parses a "fix" directive
fixstep :: Parser ProofStep
fixstep = do
   string "fix "
   vs <- varname `sepEndBy1` spaces
   return (FixStep vs)

--parses a "let" directive
letstep :: Parser ProofStep
letstep = do
   string "let ?"
   v <- varname
   string " = "
   d <- innerText
   return (LetStep v d)

-- | parses a connected step
connectedStep :: Parser ConnectedStep
connectedStep = withstep <|> try thenstep <|> try hencethus


-- parses reasoning chain
reasoning :: Parser Reasoning
reasoning = do
   is <- initStep
   spaces
   cs <- connectedStep `sepEndBy` spaces
   return ( Reasoning is cs)

-- | parses a statement starting with "moreover"
moreoveritem :: String -> Parser Reasoning
moreoveritem s = do
   string s
   spaces
   r <- reasoning
   return r

-- | parses one moreover body, that is a construct like
-- moreover A
-- moreover B
-- ultimately
-- also parses "also" construct

moreoverbody :: String -> Parser MoreoverBody
moreoverbody s = do
   items <- (moreoveritem s) `sepEndBy1` spaces
   if s=="also" then string "finally" else string "ultimately"
   spaces
   --pc <- proofcomhaveshow
   pc <- proofcom
   spaces
   cs <- connectedStep `sepEndBy` spaces
   return MoreoverBody { mrvalso = s
                       , mrvMrvs = items
                       , ultimfinal = pc
                       , followup = cs }

-- | Parses a reasoning that can have a chain of moreover or also constructs like say
-- have A by simp            *
-- then have B by auto       * reasoning
-- moreover                  -
-- have C by blast           -
-- then have C' by simp      -
-- moreover have D by simp   -
-- ultimately have E by auto - MoreoverBody
-- hence "G=H" bu simp       +
-- also have "H=F"           +
-- finally have              + MoreoverBody

longreasoning :: Parser ProofStep
longreasoning = do
   ir <- reasoning
   spaces
   mbs <- sepEndBy((try $ moreoverbody "also") <|> moreoverbody "moreover") spaces
   return (LongReasoning ir mbs)


-- | parses the "next" as a proof step
next :: Parser ProofStep
next = do
   string "next"
   return Next


-- parses a proof step
proofstep :: Parser ProofStep
proofstep = letstep <|> try fixstep <|>  try longreasoning <|>
   try next -- longreasoning may start with "note" which starts like "next", that's why we need to try it
   <?> "could not parse a proof step"

-- parses a long proof
longproof :: Parser Proof
longproof = do
   string "proof"
   spaces
   d <- option ' ' (char '-')
   spaces
   ps <- proofstep `sepEndBy1` spaces
   string "qed"
   return (LongProof { dash = (d == '-'), proofSteps = ps } )

-- | parses a proof
proof :: Parser Proof
proof = longproof <|>
        (try shortProofByTac) <|> shortProofByRule <|>
        (try $ shortProofRefTac "using") <|> (shortProofRefTac "unfolding") <?> "parsing a proof failed"

-- | parses local references starting from "from" or "with" or "note"
locrefs :: String -> Parser [String]
locrefs s = do
   string s
   spaces
   r <- labelRef `sepEndBy1` spaces
   return r


-- | converts a list of Either's to a list of values, stopping at error
eithers2vals :: [Either ParseError a] -> [a]
eithers2vals = map either2val
   where
      either2val (Left err) = error ("parse error at " ++ (show err) )
      either2val (Right x)  = x

-- | parses a list of theory texts
parseTheories :: [(String,String)] -> [Theory]
parseTheories = eithers2vals . map (\(n,t) -> (parse theoryParser n) (prepTheory t) )


-- | preprocesses a string with a theory by removing comments
-- and semicolons. We need to add a space to work around
-- the fact that appBetween does not work when the
-- string begins with a beginning mark
prepTheory :: String -> String
prepTheory = ( filter (/=';') ) . ( dropWhile (/='s') ). ( appBetween (\x-> []) "(*" "*)" ) . ( ' ': )

-- | test with parseTest theoryParser x
