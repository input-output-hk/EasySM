{-# OPTIONS --erasure --no-projection-like #-}

-- DFA (deterministic finite automata) definitions in functional style.
--
module EasySM.Functional.DFA where

open import Haskell.Prelude


-- Functional definition of a deterministic finite automaton
--
record DFA (state : Type) (label : Type) : Type₁ where
  no-eta-equality
  constructor MkDFA
  field
    transition : state → label → Maybe state
    initial    : state
    isFinal    : state → Bool
open DFA public
{-# COMPILE AGDA2HS DFA #-}

