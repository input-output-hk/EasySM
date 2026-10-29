{-# OPTIONS --erasure #-}

-- Statements of correspondence between the functional and relational DFA definitions.
--
module EasySM.Correspondence.DFA where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)

open import Haskell.Prelude                       using (Just; True)

import EasySM.Functional.DFA
import EasySM.Relational.DFA


infix 3 _⇔_
infixr 5 _∧_

_∧_ : Set → Set → Set
_∧_ = _×_

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) ∧ (B → A)

record Correctness 
         (Q : Set) (Σ : Set)
         (functionalDFA : EasySM.Functional.DFA.DFA Q Σ)
         (relationalDFA : EasySM.Relational.DFA.DFA Q Σ)
         : Set
  where

    open EasySM.Functional.DFA.DFA
    open EasySM.Relational.DFA.DFA
   
    field    
      initial_correct    : relationalDFA .q₀ ≡ functionalDFA .initial
      final_correct      : ∀ q → relationalDFA .F q ⇔ functionalDFA .isFinal q ≡ True
      transition_correct : ∀ q l q′ → relationalDFA .δ q l q′ ⇔ functionalDFA .transition q l ≡ Just q′
      