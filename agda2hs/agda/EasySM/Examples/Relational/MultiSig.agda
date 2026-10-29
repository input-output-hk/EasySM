module EasySM.Examples.Relational.MultiSig where

open import Data.Unit                             using (⊤)
open import Data.Nat                              using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Maybe.Base as Maybe              using (Maybe; nothing; just; maybe′)
open import Data.List                             using (List; _∷_; []; length)
open import Relation.Unary                        using (Pred; ∅)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EasySM.Relational.DFA                using (DFA)
open import EasySM.Relational.Augmented          using (Value; KeyHash; Pred₀; Augmentable; augment; Conf; _××_; Valued; _$>_; AugmentedAutomaton)


-- Base DFA
--

-- DFA states
--
data State : Set where
  holding collecting : State

-- DFA labels
--
data Label : Set where
  propose add pay cancel : Label

-- DFA transitions as instances
--
data _—[_]→_ : State → Label → State → Set where
  instance
    propose : holding    —[ propose ]→ collecting
    add     : collecting —[ add     ]→ collecting
    pay     : collecting —[ pay     ]→ holding
    cancel  : collecting —[ cancel  ]→ holding

multiSigDFA : DFA State Label
multiSigDFA = record { δ = _—[_]→_; q₀ = holding; F = ∅ }


-- Helper types
--

PayTo : Set
PayTo = Valued KeyHash

record Payment : Set where
  field
    value    : Value
    receiver : KeyHash
    deadline : ℕ
open Payment

-- Indexed configuration state as augmented DFA states
--
data State⁺ : Pred₀ State where
  holding    : State⁺ holding
  collecting : Payment → List KeyHash → State⁺ collecting

-- Indexed actions as augmmented DFA labels
--
data Label⁺ : Pred₀ Label where
  propose : Payment → Label⁺ propose
  add     : KeyHash → Label⁺ add
  pay     : Label⁺ pay
  cancel  : Label⁺ cancel

instance Aug-State = augment State⁺
         Aug-Label = augment Label⁺

open Augmentable ⦃...⦄

-- Intial automata states
--
initial : Value → Conf holding
initial val = record { state = holding; value = val }


open Payment

postulate
  isAuthorisedKey : KeyHash → Set  -- How do we define that properly?
  noRequiredSignatures : ℕ

private variable
  val val' : Value
  tick tick' : ℕ
  payment : Payment
  key : KeyHash
  keys : List KeyHash

-- Configuration relation
--
data _∙_⇒[_]_∙_＃_ : {s s' : State} {l : Label}
                  → Conf s
                  → List (Valued ⊤)
                  → l ⁺
                  → Conf s'
                  → List PayTo
                  → ℕ
                  → ⦃ s —[ l ]→ s' ⦄
                  → Set
  where

    ⇒-propose :
        tick < payment .deadline
      → payment .value < val
        --------------------
      → holding ×× val ∙ []
        ⇒[ propose payment ]
        collecting payment [] ×× val ∙ []
        ＃ tick

    ⇒-add :
        isAuthorisedKey key
        -------------------
      → collecting payment keys ×× val ∙ []
        ⇒[ add key ]
        collecting payment (key ∷ keys) ×× val ∙ []
        ＃ tick

    ⇒-pay :
        tick ≤ payment .deadline
      → noRequiredSignatures ≤ length keys
      → val' + payment .value ≡ val
        ---------------------------
      → collecting payment keys ×× val ∙ []
        ⇒[ pay ]
        holding ×× val' ∙ (payment .value $> payment .receiver) ∷ []
        ＃ tick

    ⇒-cancel :
        payment .deadline < tick'
        ----------------------------------------
      → collecting payment keys ×× val ∙ []
        ⇒[ cancel ]
        holding ×× val ∙ []
        ＃ tick

multiSigAA : AugmentedAutomaton State Label multiSigDFA ⊤ KeyHash
multiSigAA = record { Q⁺ = State⁺; Σ⁺ = Label⁺; δ⁺ = _∙_⇒[_]_∙_＃_; q₀⁺ = holding }
