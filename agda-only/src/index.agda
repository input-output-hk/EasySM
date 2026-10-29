----------------------------------------------------------------------------------------------------

-- TODO: licensing; portions based on my work licensed as CC-BY-SA

-- TODO: ensure DFA states and labels are finite

-- TODO: abstract Value to allow using integers in Counter-DFA; state and prove invariant in
--   Counter-ADFA

-- TODO: finish auction example

-- TODO: ensure level polymorphism actually works as intended, including in macros

-- TODO: clean up term parser

-- TODO: redefine atom to ensure string is non-empty

-- TODO: define weak bisimilarity of machines

-- TODO: use trailed colist to define corun variant that also returns final machine

-- TODO: StdReflection should re-export Pattern

-- TODO: Data.String.Literals should re-export IsString and fromString, and declare isString as
--   instance; perhaps it should even be moved to Agda.Builtin.FromString; same with other literals

-- TODO: why does StdIO use polymorphic unit?

-- TODO: why is StdIO._>>=_ not synonymous with StdIO.bind?

-- TODO: termination checker fails when using StdIO._>>=_ and do-notation in all three variants
--   of sequence for colists; stdlib authors seem to be semi-aware of this, because e.g.
--   StdIO.Colist.sequence is not written using StdIO._>>=_, but inlines its definition

-- TODO: according to Andreas Abel (personal communication, 2025), Codata.Sized.Colist
--   is not safe to use, because it is defined incorrectly, using Codata.Sized.Thunk

-- TODO: forgetting to import Relation.Nullary should result in better error message

-- TODO: perhaps Agda.Builtin.Size.∞ should be renamed to Sizeω


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module index where

import Prelude

import Machine
import Lexer
import Parser

import DFA
import DFA.Counter
import DFA.Multisig
import DFA.Auction
import IODA
import IODFA
import ADFA
import ADFA.Counter
import ADFA.Multisig
import SADFA
import SADFA.Multisig
import SADFA.Auction-V1
import SADFA.Auction-V2

import Main


----------------------------------------------------------------------------------------------------

import tmp.Colist

import tmp.ADA
import tmp.ADA.Multisig

-- TODO: clean this up
import tmp.tmp
import tmp.tmp2


----------------------------------------------------------------------------------------------------
