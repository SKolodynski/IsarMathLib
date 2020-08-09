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


module ProcessThys
   where

import qualified Data.Map as M
import Data.List(nub)

import IMLP_datatypes

-- | this module deals with processing information obtained
-- by parsing theory files. For now it extracts the list of
-- definitions and theorems from the theories.

-- | the main function exported from the module -
-- takes a list of parsed theories and returns a structure
-- with oll kinds of information that is needed

processTheories :: [Theory] -> KnowledgeBase
processTheories tt =
   KnowledgeBase { kbformalitems = getThmsDefsFromTheories tt
                 , kbtheories = map getTheoryInfo tt }

-- | extracts useful information from a single theory
getTheoryInfo :: Theory -> TheoryInfo
getTheoryInfo t = TheoryInfo { tiname = name t
                             , titheory = t
                             , tideps = getDepsFromTheory t
                             }

-- | gets the name from a formal item in simple form:
getSFIname :: SimpleFormalItem -> String
getSFIname (SimpleProp _ _ nm _ _ _) = nm
getSFIname (SimpleDef nm _ ) = nm ++ "_def"
getSFIname OtherSimpleItem = "a context"

-- | converts a formal item to a a simplified form.
formal2simple :: FormalItem -> SimpleFormalItem

formal2simple (Definition name _ _ _ def) = SimpleDef name def

formal2simple (FormalItem prop) =
   SimpleProp { sproptype = proptype prop
              , scontext  = context prop
              , spropname = propname prop
              , sproprems= propprems prop
              , sclaims   = claims prop
              , sdeps = getDepsFromProposition prop
              }

formal2simple _ = OtherSimpleItem

-- | gets all the formal items in th simple form from a section
getThmsDefsFromSec :: Subsection -> [SimpleFormalItem]
getThmsDefsFromSec (Subsection tit intro ims) =
   map (formal2simple . formalItem) ims

-- | gets all formal items from a theory in simple form
getThmsDefsFromThry :: Theory -> [FormalItemInfo]
getThmsDefsFromThry t =
   map (addTheoryName (name t)) (concat $ map getThmsDefsFromSec (thsections t))

-- | converts a list of simple formal items into a list of
-- formal item infos by adding the name of theory
addTheoryName :: String -> SimpleFormalItem -> FormalItemInfo
addTheoryName nme item = FormalItemInfo { fimTheoryName = nme, fimitem = item }

-- | gets all formal items in simple form from a list
-- of theories
getThmsDefsFromTheories :: [Theory] -> [FormalItemInfo]
getThmsDefsFromTheories = concat . map getThmsDefsFromThry

-- get dependencies from a Theory
getDepsFromTheory :: Theory ->  [String]
getDepsFromTheory t =
   nub $ (map nmAfterDot) $ concatMap getDepsFromSubsection (thsections t)
   where nmAfterDot = reverse . takeWhile (/='.') . reverse

-- get dependencies from a Subsection
getDepsFromSubsection :: Subsection -> [String]
getDepsFromSubsection sec =
   concatMap (getDepsFromFormalItem . formalItem) (items sec)

-- get dependencies from formal Item
getDepsFromFormalItem :: FormalItem -> [String]
getDepsFromFormalItem  (FormalItem p) = getDepsFromProposition p
getDepsFromFormalItem _ = []

-- get dependencies from a formal item, for now only theorems
getDepsFromProposition :: Proposition -> [String]
getDepsFromProposition = getDepsFromProof . propproof

-- | gets dependencies from a proof
getDepsFromProof :: Proof -> [String]
getDepsFromProof (UsingBy _ d _ d1 _ ) = d ++ d1
getDepsFromProof (ByRule s) = [s]
getDepsFromProof (LongProof _  pss) = concatMap getDepsFromProofStep pss

-- | gets dependencies from a proof step
getDepsFromProofStep :: ProofStep -> [String]

getDepsFromProofStep (LongReasoning r mbs) =
   (getDepsFromReasoning r) ++ (concatMap getDepsFromMoreoverBody mbs)

getDepsFromProofStep _ = []

-- | gets dependencies from reasoning
getDepsFromReasoning :: Reasoning -> [String]
getDepsFromReasoning (Reasoning is css) =
   (getDepsFromInitStep is) ++ (concatMap getDepsFromConnectedStep css)

-- | gets dependencies from InitStep
getDepsFromInitStep :: InitStep -> [String]
getDepsFromInitStep (InitStep _ pc) = getDepsFromProofCommand pc
getDepsFromInitStep (StepBlock sbs) = concatMap getDepsFromProofStep sbs
getDepsFromInitStep _ = []


-- | gets dependencies from a MoreoverBody
getDepsFromMoreoverBody :: MoreoverBody -> [String]
getDepsFromMoreoverBody (MoreoverBody _ rss pc css) =
   (concatMap getDepsFromReasoning rss) ++ (getDepsFromProofCommand pc) ++
   (concatMap getDepsFromConnectedStep css)

-- | gets dependencies from a ConnectedStep
getDepsFromConnectedStep :: ConnectedStep -> [String]
getDepsFromConnectedStep (WithStep _ pc) = getDepsFromProofCommand pc
getDepsFromConnectedStep (ThenStep pc) = getDepsFromProofCommand pc
getDepsFromConnectedStep _ = []

-- | gets dependencies from a ProofCommand
getDepsFromProofCommand :: ProofCommand -> [String]
getDepsFromProofCommand (PChaveShow _ cp) = getDepsFromClaimProof cp
getDepsFromProofCommand (PCbtain _ cp) = getDepsFromClaimProof cp

-- | gets dependencies from a ClaimProof
getDepsFromClaimProof :: ClaimProof -> [String]
getDepsFromClaimProof (ClaimProof _ p) = getDepsFromProof p

-- | true if the formal item is a proposition
-- (rather than definition or locale)
isProposition :: FormalItemInfo -> Bool
isProposition (FormalItemInfo _  (SimpleProp _  _  _  _  _ _)) = True
isProposition _ = False

-- | true if the formal item is a definition
-- (rather than a proposition or locale)
isDefinition :: FormalItemInfo -> Bool
isDefinition (FormalItemInfo _  (SimpleDef _ _)) = True
isDefinition _ = False
