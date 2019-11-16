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

module IMLP_datatypes
   where

-- | this file provides a data structure that we parse IsarMathLib
-- sources to proof language. This includes the formal part -
-- definitions, theorems and contexts as well as the informal comments.

-- | The structure for an IsarMatlib theory
data Theory =
   Theory  { header   :: String
           , name     :: String
           , imports  :: [String]
           , thIntro  :: String
           , thsections  :: [Subsection]
           } deriving (Eq, Show)

-- | useful data extracted from one parsed theory
data TheoryInfo =
   TheoryInfo { tiname   :: String -- redundant, but useful
              , titheory :: Theory -- parsed theory
              , tideps   :: [String] -- a list of all dependencies in theory
              }

-- | useful data extracted from all theories
data KnowledgeBase =
   KnowledgeBase { kbformalitems :: [FormalItemInfo] -- common for all theories
                 , kbtheories :: [TheoryInfo] -- a list of information about theories
                 }

-- | a structure for a section
data Subsection =
   Subsection { sectitle    :: String,
             secIntro    :: String,
             items       :: [Item]
           } deriving (Eq, Show)

-- | a structure holding a formal item (definition, theorem or a
-- context) with its informal description. Note we enforce convention
-- that each formal item needs a description.
data Item =
   Item { description :: String,
          formalItem  :: FormalItem
        } deriving (Eq, Show)


-- | The formal part of an item
data FormalItem =
   Definition { defname :: String -- maybe explicit or extracted from the actual definition
              , defcontext  :: String -- an optional locale
              , deftypespec :: String -- optional
              , deflabel :: (String, Bool) -- optional, String is the label, Bool here means the presence of [simp] modifier
              , def :: String }
   | Abbreviation   { abbname :: String
                    , abbnotation :: String -- string defining notation, like "_ ->F _ {in} _"
                    , abbspec :: String -- the actual abbreviation (after the "where" keyword)
                    }
   | Locale { localename  :: String
            , inheritsFrom :: (String,[String]) -- we are supporting only one parent: locale1 = locale0 + [localeItems]
            , localeItems :: [LocaleItem] }
   | FormalItem Proposition
   deriving (Eq, Show)


-- | different statements that can show up in a locale definition
data LocaleItem = Fixes [NameNotation] -- a list of names of variables with their notations
                | Defines { locdefNameSimp :: (String, Bool) -- name may be with simp or not
                          , locdef :: String }
                | Assumes [(String,[String])]
                deriving (Eq, Show)

-- | a single variable in the "fixes" locale item with an optional notation,
-- something like gmult (infixl "\<cdot>" 70)
data NameNotation = NameNotation { fixedName :: String, fixedNotation :: String }
                deriving (Eq, Show)

-- | premises in a theorem
data PropPremise = PropDefines [(String,[String])] | PropAssumes [(String,[String])]
                deriving (Eq, Show)

-- | a structure for a proposition
data Proposition = Proposition {
   proptype :: String, -- may be "theorem", "lemma" or "corollary"
   context  :: String, -- an optional locale
   propname  :: String,
   propprems :: [PropPremise],
   claims    :: [(String,[String])],
   propproof :: Proof }
   deriving (Eq, Show)


-- | a short version of formal item structure for storing information
-- in the theorem database
data FormalItemInfo = FormalItemInfo { fimTheoryName :: String,
                                       fimitem :: SimpleFormalItem }
                                       deriving (Eq, Show)


data SimpleFormalItem = SimpleProp { sproptype :: String
                             , scontext  :: String
                             , spropname :: String
                             , sproprems :: [PropPremise]
                             , sclaims   :: [(String,[String])]
                             , sdeps :: [String] -- names of dependencies
                             }
                         | SimpleDef String String
                         | OtherSimpleItem
                         deriving (Eq, Show)


data Proof = UsingBy { useunfold :: String -- "using" or "unfolding"
                     , usedprops :: [String] -- a list of references
                     , ptactic :: String -- a tactic: simp, auto, etc
                     }
           | ByRule String
           | LongProof
              { dash :: Bool -- does it have a dash or not?
              , proofSteps :: [ProofStep]
              }
           deriving (Eq, Show)

-- | a statement with a prooof
data ClaimProof = ClaimProof { cpclaims :: [(String,[String])]
                             , cpproof :: Proof }
                  deriving (Eq, Show)

-- | have or obtain smth with a proof
data ProofCommand = PChaveShow String ClaimProof -- the String is "have" or "show"
                  | PCbtain [String] ClaimProof -- the [String] is the list of variables to obtain
                  deriving (Eq, Show)

-- | a proof step from which a chain of connected steps can start
data InitStep = InitStep [String] ProofCommand
                   | StepBlock [ProofStep]
                   | Assume [(String,[String])]
                   | Note [String]
                   deriving (Eq, Show)

-- | these are types of steps that use facts from the previous step
data ConnectedStep = WithStep [String] ProofCommand
                   | ThenStep ProofCommand
                   | HenceThus { henceorthus :: String
                               , ttclaims     :: [(String,[String])]
                               , tttactic     :: String }
                   deriving (Eq, Show)

-- | a chain of connected stepslike have ... , with ... have ..., then have ... and so on
data Reasoning = Reasoning InitStep [ConnectedStep]
                    deriving (Eq, Show)


-- | This structure holds the part of the "moreover" (or "also")
-- construct that starts with the first "moreover" (or "also" keyword)
data MoreoverBody = MoreoverBody { mrvalso :: String -- indicates if this is a moreover or also construct
                                 , mrvMrvs :: [Reasoning]
                                 , ultimfinal :: ProofCommand
                                 , followup :: [ConnectedStep] }
                  deriving (Eq, Show)

-- the whole proof step that in fact may contain a lot of steps.
-- Most of the time the list [MoreoverBody] is empty and then we don't
-- have the "moreover" construct but just a chain of connected steps.
data ProofStep =  LongReasoning Reasoning [MoreoverBody] -- maybe short as the list may be empty, covers also the also construct
               | FixStep [String]
               | LetStep String String
               | Next
               deriving (Eq, Show)











