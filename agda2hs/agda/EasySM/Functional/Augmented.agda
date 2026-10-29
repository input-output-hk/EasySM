{-# OPTIONS --erasure --no-projection-like #-}
module EasySM.Functional.Augmented where

open import Haskell.Prelude

open import EasySM.Functional.DFA
open DFA


KeyHash = List Char
{-# COMPILE AGDA2HS KeyHash #-}

Value = Nat
{-# COMPILE AGDA2HS Value #-}

-- The type class of augmentable types.
--
-- NB: `Augmentable` is kept for the Correspondence module, which uses it to relate
-- the functional and relational versions. The functional `AugmentedAutomaton` does
-- not use `Augmentable` — it uses plain type parameters (`sPlus`, `lPlus`) instead
-- of the type family `_⁺`, so that agda2hs can compile it to Haskell.
--
record Augmentable (a : Type) : Type₁ where
  no-eta-equality
  constructor Augment
  field _⁺ : a → Type
open Augmentable ⦃...⦄ public
{-# COMPILE AGDA2HS Augmentable existing-class #-}

-- Automata configuration: a base state, its augmented version, and a value.
--
-- The augmented state type `aug` is a plain type parameter. In the Correspondence
-- module, it is instantiated with `s ⁺` (the relational augmented type).
--
record Conf (q : Type) (aug : Type) : Type where
  no-eta-equality
  constructor MkConf
  field
    baseState : q
    augState  : aug
    value     : Value
open Conf public
{-# COMPILE AGDA2HS Conf #-}

-- Enrich a datum with a value
--
record Valued (d : Type) : Type where
  no-eta-equality
  constructor MkValued
  field
    amount : Value
    datum  : d
open Valued public
{-# COMPILE AGDA2HS Valued #-}

-- Add up all the values in a list of valued entities.
--
listValue : {a : Type} → List (Valued a) → Value
listValue = foldl (λ s e → s + Valued.amount e) 0
{-# COMPILE AGDA2HS listValue #-}


-- The result of an augmented transition: the next state, its configuration,
-- the produced outputs, and the clock tick.
--
-- The augmented state type `sPlus'` is a plain type parameter. In the Correspondence
-- module, it is instantiated with `s' ⁺` (the relational augmented type of the target state).
--
record StepResult (q : Type) (sPlus' : Type) (input output : Type) : Type where
  no-eta-equality
  constructor MkStepResult
  field
    nextState  : q
    nextConf   : Conf q sPlus'
    outputs    : List (Valued output)
    resultTick : Nat
open StepResult public
{-# COMPILE AGDA2HS StepResult #-}


-- An augmented DFA has got states and labels that are augmented states and labels of the underlying DFA.
--
-- * Transitions of the augmented DFA are functions from automata configurations (which in turn embed augmented DFA states)
--   and augmented DFA labels to the next configuration. A transition is only possible with a particular augmented label
--   if the unadorned states of the related configurations admit a transition in the underlying DFA with the unadorned label. In
--   other words, transitions of the augmented automaton are augmented transitions of the DFA.
--
-- * In addition to augmented configurations and an augmented label, a transition of the augmented automaton also involves a list
--   of inputs, a list of outputs, and a tick (of a logical clock). Inputs and outputs are consumed and produced by the transition,
--   respectively.
--
-- NB: This version uses plain type parameters (`sPlus`, `lPlus`) instead of the type family `_⁺`
-- so that agda2hs can compile it to Haskell. The connection between base types and augmented types
-- is established in the Correspondence module, where `sPlus` is instantiated with `s ⁺`.
--
record AugmentedAutomaton
         (q : Type) (l : Type)
         (sPlus : Type) (lPlus : Type)
         (input  : Type)
         (output : Type)
         : Type₁
       where
  no-eta-equality
  constructor MkAugmentedAutomaton
  field
    deltaPlus : Conf q sPlus
              → Nat
              → List (Valued input)
              → lPlus
              → Maybe (StepResult q sPlus input output)
    q0Plus    : sPlus
open AugmentedAutomaton public
{-# COMPILE AGDA2HS AugmentedAutomaton #-}
