{-# OPTIONS --erasure #-}

-- Statements of correspondence between the functional and relational augmented automaton definitions.
--
module EasySM.Correspondence.Augmented where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function                             using (id)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import Data.Nat                              using (ℕ)
open import Data.List                             using (List; map)

open import Haskell.Prelude                       using (Just; True; Nat)

import EasySM.Functional.DFA
import EasySM.Relational.DFA
import EasySM.Functional.Augmented as F
import EasySM.Relational.Augmented as R
import EasySM.Correspondence.DFA

open import EasySM.Correspondence.DFA using (_⇔_; _∧_)


-- Convert between Nat (functional) and ℕ (relational).
-- These are structurally identical but distinct types.
--
postulate
  natToℕ : Nat → ℕ
  ℕToNat : ℕ → Nat


-- Local abbreviations for the augmented type, disambiguating the functional
-- and relational Augmentable instances.
--
open F.Augmentable ⦃...⦄ renaming (_⁺ to augF)
open R.Augmentable ⦃...⦄ renaming (_⁺ to augR)


-- Convert a relational Valued to a functional Valued.
--
relValued→funValued : ∀ {D : Set} → R.Valued D → F.Valued D
relValued→funValued v = F.MkValued
  (ℕToNat (R.Valued.value v))
  (R.Valued.datum v)

-- Convert a functional Valued to a relational Valued.
--
funValued→relValued : ∀ {D : Set} → F.Valued D → R.Valued D
funValued→relValued v = record
  { value = natToℕ (F.Valued.amount v)
  ; datum = F.Valued.datum v
  }


-- Convert a relational Conf to a functional Conf.
--
-- The `agree` parameter states that the functional and relational Augmentable
-- instances agree on `_⁺`, so `s ⁺` is the same type in both worlds.
--
relConf→funConf : ∀ {Q : Set} {s : Q}
                 ⦃ aug-rel : R.Augmentable Q ⦄ ⦃ aug-fun : F.Augmentable Q ⦄ →
                 (∀ s → (augF s) ≡ (augR s)) →
                 R.Conf s → F.Conf Q (augF s)
relConf→funConf {s = s} agree c = F.MkConf s
  (subst id (sym (agree s)) (R.Conf.state c))
  (ℕToNat (R.Conf.value c))

-- Convert a functional Conf to a relational Conf.
--
funConf→relConf : ∀ {Q : Set} {s : Q}
                 ⦃ aug-rel : R.Augmentable Q ⦄ ⦃ aug-fun : F.Augmentable Q ⦄ →
                 (∀ s → (augF s) ≡ (augR s)) →
                 F.Conf Q (augF s) → R.Conf s
funConf→relConf {s = s} agree c = record
  { state = subst id (agree s) (F.Conf.augState c)
  ; value = natToℕ (F.Conf.value c)
  }


-- Correctness of an augmented automaton: the functional and relational versions agree.
--
-- The functional AugmentedAutomaton uses plain type parameters (sPlus, lPlus) instead of
-- the type family _⁺. The correspondence instantiates sPlus with the augmented type of
-- the source state, and lPlus with the augmented type of the label.
--
record Correctness
         (Q : Set) (Σ : Set)
         (sPlus : Set) (lPlus : Set)
         (functionalDFA : EasySM.Functional.DFA.DFA Q Σ)
         (relationalDFA : EasySM.Relational.DFA.DFA Q Σ)
         (dfaCorrectness : EasySM.Correspondence.DFA.Correctness Q Σ functionalDFA relationalDFA)
         ⦃ aug-state-fun : F.Augmentable Q ⦄
         ⦃ aug-label-fun : F.Augmentable Σ ⦄
         ⦃ aug-state-rel : R.Augmentable Q ⦄
         ⦃ aug-label-rel : R.Augmentable Σ ⦄
         (input  : Set)
         (output : Set)
         (functionalAA : F.AugmentedAutomaton Q Σ sPlus lPlus input output)
         (relationalAA : R.AugmentedAutomaton Q Σ relationalDFA input output)
         : Set₁
  where
    field
      -- The Augmentable instances agree on the augmented type.
      --
      augmentable_state_correct : ∀ s → (augF s) ≡ (augR s)
      augmentable_label_correct : ∀ l → (augF l) ≡ (augR l)

      -- sPlus corresponds to the augmented type of the source state.
      --
      sPlus_correct : ∀ s → sPlus ≡ (augF s)

      -- lPlus corresponds to the augmented type of the label.
      --
      lPlus_correct : ∀ l → lPlus ≡ (augF l)

      -- δ⁺ correspondence: the relational transition relation holds iff the functional
      -- transition function returns `Just` with the corresponding step.
      --
      -- The functional δ⁺ returns a StepResult with the source state's augmented type (sPlus).
      -- The correspondence matches the nextState, outputs, and tick; the nextConf field
      -- is at the target state but typed with sPlus (source augmented type) — this is
      -- the known unsoundness of the functional version.
      --
      δ⁺_correct-forward : ∀ {s s' : Q} {l : Σ}
                   (conf     : R.Conf s)
                   (inputs   : List (R.Valued input))
                   (augLabel : augR l)
                   (conf'    : R.Conf s')
                   (outputs  : List (R.Valued output))
                   (tick     : ℕ)
                   ⦃ dfa-trans : (relationalDFA .EasySM.Relational.DFA.DFA.δ) s l s' ⦄ →
        (relationalAA .R.AugmentedAutomaton.δ⁺ conf inputs augLabel conf' outputs tick) →
        (functionalAA .F.AugmentedAutomaton.deltaPlus
          (subst (λ aug → F.Conf Q aug) (sym (sPlus_correct s))
            (relConf→funConf augmentable_state_correct conf))
          (ℕToNat tick)
          (map relValued→funValued inputs)
          (subst id (sym (lPlus_correct l))
            (subst id (sym (augmentable_label_correct l)) augLabel))
          ≡ Just (F.MkStepResult s'
                  (subst (λ aug → F.Conf Q aug) (sym (sPlus_correct s'))
                    (relConf→funConf augmentable_state_correct conf'))
                  (map relValued→funValued outputs)
                  (ℕToNat tick)))

      δ⁺_correct-backward : ∀ {s s' : Q} {l : Σ}
                   (conf     : R.Conf s)
                   (inputs   : List (R.Valued input))
                   (augLabel : augR l)
                   (conf'    : R.Conf s')
                   (outputs  : List (R.Valued output))
                   (tick     : ℕ)
                   ⦃ dfa-trans : (relationalDFA .EasySM.Relational.DFA.DFA.δ) s l s' ⦄ →
        (functionalAA .F.AugmentedAutomaton.deltaPlus
          (subst (λ aug → F.Conf Q aug) (sym (sPlus_correct s))
            (relConf→funConf augmentable_state_correct conf))
          (ℕToNat tick)
          (map relValued→funValued inputs)
          (subst id (sym (lPlus_correct l))
            (subst id (sym (augmentable_label_correct l)) augLabel))
          ≡ Just (F.MkStepResult s'
                  (subst (λ aug → F.Conf Q aug) (sym (sPlus_correct s'))
                    (relConf→funConf augmentable_state_correct conf'))
                  (map relValued→funValued outputs)
                  (ℕToNat tick))) →
        (relationalAA .R.AugmentedAutomaton.δ⁺ conf inputs augLabel conf' outputs tick)

      -- q₀⁺ correspondence: the initial state augmentation agrees.
      --
      -- The functional q0Plus has type sPlus; the relational q₀⁺ has type Q⁺ (dfa .q₀).
      -- The sPlus_correct field already relates sPlus to augF s for any s.
      --
      q₀⁺_correct : sPlus ≡ (augF (functionalDFA .EasySM.Functional.DFA.DFA.initial))
