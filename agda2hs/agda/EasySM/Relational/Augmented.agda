module EasySM.Relational.Augmented where

open import Level
open import Data.Nat                              using (ℕ; _<_; _+_)
open import Data.Maybe.Base as Maybe              using (Maybe; nothing; just; maybe′)
open import Data.Product                          using (_×_; _,_)
open import Data.List                             using (List; []; _∷_; _++_; foldl)
open import Data.String                           using (String)
open import Relation.Unary                        using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EasySM.Relational.DFA
open DFA


KeyHash = String

-- FIXME: How are we going to represent token bundles?
Value = ℕ

Pred₀ : ∀ {ℓ} → Set ℓ → Set (suc 0ℓ ⊔ ℓ)
Pred₀ A = Pred A 0ℓ

-- The type class of augmentable types.
--
-- The method `_⁺` takes an augmentable type to its augmented version.
--
record Augmentable (A : Set) : Set₁ where
  constructor augment
  field _⁺ : Pred₀ A
open Augmentable ⦃...⦄ public

-- Automata configuration `s+ ×× v` as an augmented base state `s+` combined with a value `v`.
--
infix 30 _××_
record Conf {Q : Set} (s : Q) {{aug : Augmentable Q}} : Set where
  constructor _××_
  field
    state : s ⁺
    value : Value

-- Enrich a datum with a value
--
record Valued (D : Set) : Set where
  constructor _$>_
  field
    value : Value
    datum : D

-- Add up all the values in a list of valued entities.
--
listValue : {A : Set} -> List (Valued A) -> Value
listValue = foldl (λ s e → s + Valued.value e) 0


-- An augmented DFA has got states and labels that are augmented states and labels of the underlying DFA.
--
-- * Transitions of the augmented DFA relate automata configurations (which in turn embed augmented DFA states) and are labelled
--   with augmented DFA labels. Transitions between automata configurations are only possible with a particular augmented label
--   if the unadorned states of the related configurations admit a transition in the underlying DFA with the unadorned label. In
--   other words, transitions of the augmented automaton are augmented transitions of the DFA.
--
-- * In addition to augmented configurations and an augmented label, a transition of the augmented automaton also involves a list
--   of inputs, a list of outputs, and a tick (of a logical clock). Inputs and outputs are consumed and produced by the transition,
--   respectively.
--
record AugmentedAutomaton
         (Q : Set) (Σ : Set)
         (dfa : DFA Q Σ)
         ⦃ aug-state : Augmentable Q ⦄
         ⦃ aug-label : Augmentable Σ ⦄ 
         (input  : Set)
         (output : Set)
         : Set₁
       where
  field
    Q⁺  : Pred₀ Q
    Σ⁺  : Pred₀ Σ
    δ⁺  : {s s' : Q} {l : Σ}
          → Conf s
          → List (Valued input)
          → l ⁺
          → Conf s'
          → List (Valued output)
          → ℕ
          → ⦃ (dfa .δ) s l s' ⦄
          → Set
    q₀⁺ : Q⁺ (dfa .q₀)
open AugmentedAutomaton
