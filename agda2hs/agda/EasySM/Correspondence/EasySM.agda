{-# OPTIONS --erasure #-}

-- Statements of correspondence between the functional and relational EasySM definitions.
--
module EasySM.Correspondence.EasySM where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function                             using (id)
open import Haskell.Prim.Tuple using (_×_; _,_)
open import Data.Nat                              using (ℕ)
open import Data.List                             using (List; map)

open import Haskell.Prelude                       using (Just; True; Nat)

import EasySM.Functional.DFA
import EasySM.Relational.DFA
import EasySM.Functional.Augmented as F
import EasySM.Relational.Augmented as R
import EasySM.Functional.EasySM as FE
import EasySM.Relational.EasySM as RE
import EasySM.Correspondence.DFA
import EasySM.Correspondence.Augmented as CA

open import EasySM.Correspondence.DFA using (_⇔_; _∧_)
open import EasySM.Correspondence.Augmented using (natToℕ; ℕToNat; relValued→funValued; funValued→relValued; relConf→funConf; funConf→relConf)

open F.Augmentable ⦃...⦄ renaming (_⁺ to augF)
open R.Augmentable ⦃...⦄ renaming (_⁺ to augR)


-- Convert relational TimedConf fields to a functional TimedConf.
--
timedConf→fun : ∀ {Q : Set} {s : Q} {sPlus : Set}
  ⦃ aug-rel : R.Augmentable Q ⦄ ⦃ aug-fun : F.Augmentable Q ⦄ →
  (∀ s → (augF s) ≡ (augR s)) →
  (∀ s → sPlus ≡ (augF s)) →
  R.Conf s → ℕ →
  FE.TimedConf Q sPlus
timedConf→fun {Q} {s} {sPlus} agree sPlusCorrect conf tick = FE.MkTimedConf
  (subst (λ aug → F.Conf Q aug) (sym (sPlusCorrect s))
    (relConf→funConf agree conf))
  (ℕToNat tick)

-- Convert a relational step trigger action to a functional Trigger.
--
stepTrigger→fun : ∀ {Σ : Set} {l : Σ} {lPlus : Set} {input : Set}
  ⦃ aug-label-rel : R.Augmentable Σ ⦄ ⦃ aug-label-fun : F.Augmentable Σ ⦄ →
  (∀ l → (augF l) ≡ (augR l)) →
  (∀ l → lPlus ≡ (augF l)) →
  augR l →
  FE.Trigger lPlus input
stepTrigger→fun {Σ} {l} {lPlus} {input} agreeLabel lPlusCorrect action =
  FE.StepT (subst id (sym (lPlusCorrect l))
    (subst id (sym (agreeLabel l)) action))

-- Convert a relational ingress trigger message to a functional Trigger.
--
ingressTrigger→fun : ∀ {input : Set} {lPlus : Set} →
  R.Valued input →
  FE.Trigger lPlus input
ingressTrigger→fun {input} {lPlus} msg = FE.IngressT (relValued→funValued msg)


-- Correctness of EasySM: the functional and relational versions agree.
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
         (augmentable_state_correct : ∀ s → (augF s) ≡ (augR s))
         (augmentable_label_correct : ∀ l → (augF l) ≡ (augR l))
         (sPlus_correct : ∀ s → sPlus ≡ (augF s))
         (lPlus_correct : ∀ l → lPlus ≡ (augF l))
         ⦃ functionalValidator : FE.MessageValidator Q sPlus input ⦄
         (relationalValidator : RE.MessageValidator Q Σ relationalDFA input)
         : Set₁
  where
    field
      -- MessageValidator correspondence
      validator_correct : ∀ {s : Q} (conf : R.Conf s) (tick : ℕ) (msg : R.Valued input) →
        (relationalValidator .RE.MessageValidator.check conf tick msg) ⇔
        (functionalValidator .FE.MessageValidator.check
          (subst (λ aug → F.Conf Q aug) (sym (sPlus_correct s)) (relConf→funConf augmentable_state_correct conf))
          (ℕToNat tick)
          (relValued→funValued msg)
          ≡ True)

      -- step correspondence (forward)
      step_correct-forward : ∀ {s s' : Q} {l : Σ}
        (timedConf  : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s)
        (inputs     : List (R.Valued input))
        (augLabel   : augR l)
        (timedConf' : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s')
        (outputs    : List (R.Valued output))
        ⦃ dfa-trans : (relationalDFA .EasySM.Relational.DFA.DFA.δ) s l s' ⦄ →
        (RE.EasySM._∙_⇒[_]_∙_ Q Σ relationalDFA input output relationalAA relationalValidator timedConf inputs augLabel timedConf' outputs) →
        (FE.EasySM.step Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf timedConf) (RE.EasySM.TimedConf.tick timedConf))
          (map relValued→funValued inputs)
          (subst id (sym (lPlus_correct l))
            (subst id (sym (augmentable_label_correct l)) augLabel))
          ≡ Just (timedConf→fun augmentable_state_correct sPlus_correct
                    (RE.EasySM.TimedConf.conf timedConf') (RE.EasySM.TimedConf.tick timedConf') ,
                  map relValued→funValued outputs))

      -- step correspondence (backward)
      step_correct-backward : ∀ {s s' : Q} {l : Σ}
        (timedConf  : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s)
        (inputs     : List (R.Valued input))
        (augLabel   : augR l)
        (timedConf' : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s')
        (outputs    : List (R.Valued output))
        ⦃ dfa-trans : (relationalDFA .EasySM.Relational.DFA.DFA.δ) s l s' ⦄ →
        (FE.EasySM.step Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf timedConf) (RE.EasySM.TimedConf.tick timedConf))
          (map relValued→funValued inputs)
          (subst id (sym (lPlus_correct l))
            (subst id (sym (augmentable_label_correct l)) augLabel))
          ≡ Just (timedConf→fun augmentable_state_correct sPlus_correct
                    (RE.EasySM.TimedConf.conf timedConf') (RE.EasySM.TimedConf.tick timedConf') ,
                  map relValued→funValued outputs)) →
        (RE.EasySM._∙_⇒[_]_∙_ Q Σ relationalDFA input output relationalAA relationalValidator timedConf inputs augLabel timedConf' outputs)

      -- ingress correspondence (forward)
      ingress_correct-forward : ∀ {s : Q}
        (timedConf : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s)
        (inbox     : List (R.Valued input))
        (msg       : R.Valued input)
        (inbox'    : List (R.Valued input)) →
        (RE.EasySM._∙_↓[_]_ Q Σ relationalDFA input output relationalAA relationalValidator timedConf inbox msg inbox') →
        (FE.EasySM.ingress Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf timedConf) (RE.EasySM.TimedConf.tick timedConf))
          (map relValued→funValued inbox)
          (relValued→funValued msg)
          ≡ Just (map relValued→funValued inbox'))

      -- ingress correspondence (backward)
      ingress_correct-backward : ∀ {s : Q}
        (timedConf : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s)
        (inbox     : List (R.Valued input))
        (msg       : R.Valued input)
        (inbox'    : List (R.Valued input)) →
        (FE.EasySM.ingress Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf timedConf) (RE.EasySM.TimedConf.tick timedConf))
          (map relValued→funValued inbox)
          (relValued→funValued msg)
          ≡ Just (map relValued→funValued inbox')) →
        (RE.EasySM._∙_↓[_]_ Q Σ relationalDFA input output relationalAA relationalValidator timedConf inbox msg inbox')

      -- multiStep correspondence (forward)
      multiStep_correct-forward : ∀ {s final : Q}
        (timedConf  : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s)
        (inputs     : List (R.Valued input))
        (triggers   : List (RE.EasySM.Trigger Q Σ relationalDFA input output relationalAA relationalValidator))
        (finalConf  : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator final)
        (outputs    : List (R.Valued output)) →
        (RE.EasySM._∙_⇓[_]_∙_ Q Σ relationalDFA input output relationalAA relationalValidator timedConf inputs triggers finalConf outputs) →
        (FE.EasySM.multiStep Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf timedConf) (RE.EasySM.TimedConf.tick timedConf))
          (map relValued→funValued inputs)
          (map (λ { (RE.EasySM.step {l} action) → stepTrigger→fun augmentable_label_correct lPlus_correct action
                  ; (RE.EasySM.ingress msg) → ingressTrigger→fun msg }) triggers)
          ≡ Just (timedConf→fun augmentable_state_correct sPlus_correct
                    (RE.EasySM.TimedConf.conf finalConf) (RE.EasySM.TimedConf.tick finalConf) ,
                  map relValued→funValued outputs))

      -- multiStep correspondence (backward)
      multiStep_correct-backward : ∀ {s final : Q}
        (timedConf  : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator s)
        (inputs     : List (R.Valued input))
        (triggers   : List (RE.EasySM.Trigger Q Σ relationalDFA input output relationalAA relationalValidator))
        (finalConf  : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator final)
        (outputs    : List (R.Valued output)) →
        (FE.EasySM.multiStep Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf timedConf) (RE.EasySM.TimedConf.tick timedConf))
          (map relValued→funValued inputs)
          (map (λ { (RE.EasySM.step {l} action) → stepTrigger→fun augmentable_label_correct lPlus_correct action
                  ; (RE.EasySM.ingress msg) → ingressTrigger→fun msg }) triggers)
          ≡ Just (timedConf→fun augmentable_state_correct sPlus_correct
                    (RE.EasySM.TimedConf.conf finalConf) (RE.EasySM.TimedConf.tick finalConf) ,
                  map relValued→funValued outputs)) →
        (RE.EasySM._∙_⇓[_]_∙_ Q Σ relationalDFA input output relationalAA relationalValidator timedConf inputs triggers finalConf outputs)

      -- run correspondence (forward)
      run_correct-forward : ∀ {final : Q}
        (initialConf : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator (relationalDFA .EasySM.Relational.DFA.DFA.q₀))
        (triggers    : List (RE.EasySM.Trigger Q Σ relationalDFA input output relationalAA relationalValidator))
        (finalConf   : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator final)
        (outputs     : List (R.Valued output)) →
        (RE.EasySM._⇓[_]_∙_ Q Σ relationalDFA input output relationalAA relationalValidator initialConf triggers finalConf outputs) →
        (FE.EasySM.run Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf initialConf) (RE.EasySM.TimedConf.tick initialConf))
          (map (λ { (RE.EasySM.step {l} action) → stepTrigger→fun augmentable_label_correct lPlus_correct action
                  ; (RE.EasySM.ingress msg) → ingressTrigger→fun msg }) triggers)
          ≡ Just (timedConf→fun augmentable_state_correct sPlus_correct
                    (RE.EasySM.TimedConf.conf finalConf) (RE.EasySM.TimedConf.tick finalConf) ,
                  map relValued→funValued outputs))

      -- run correspondence (backward)
      run_correct-backward : ∀ {final : Q}
        (initialConf : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator (relationalDFA .EasySM.Relational.DFA.DFA.q₀))
        (triggers    : List (RE.EasySM.Trigger Q Σ relationalDFA input output relationalAA relationalValidator))
        (finalConf   : RE.EasySM.TimedConf Q Σ relationalDFA input output relationalAA relationalValidator final)
        (outputs     : List (R.Valued output)) →
        (FE.EasySM.run Q Σ sPlus lPlus input output functionalDFA functionalAA
          (timedConf→fun augmentable_state_correct sPlus_correct
            (RE.EasySM.TimedConf.conf initialConf) (RE.EasySM.TimedConf.tick initialConf))
          (map (λ { (RE.EasySM.step {l} action) → stepTrigger→fun augmentable_label_correct lPlus_correct action
                  ; (RE.EasySM.ingress msg) → ingressTrigger→fun msg }) triggers)
          ≡ Just (timedConf→fun augmentable_state_correct sPlus_correct
                    (RE.EasySM.TimedConf.conf finalConf) (RE.EasySM.TimedConf.tick finalConf) ,
                  map relValued→funValued outputs)) →
        (RE.EasySM._⇓[_]_∙_ Q Σ relationalDFA input output relationalAA relationalValidator initialConf triggers finalConf outputs)
