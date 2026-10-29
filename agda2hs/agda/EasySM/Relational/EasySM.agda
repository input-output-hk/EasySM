module EasySM.Relational.EasySM where

open import Level
open import Data.Nat                              using (ℕ; _<_; _+_)
open import Data.Maybe.Base as Maybe              using (Maybe; nothing; just; maybe′)
open import Data.Product                          using (_×_; _,_)
open import Data.List                             using (List; []; _∷_; _++_; foldl)
open import Relation.Unary                        using (Pred)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EasySM.Relational.DFA
open DFA
open import EasySM.Relational.Augmented
open AugmentedAutomaton


record MessageValidator
         (Q : Set) (Σ : Set)
         (dfa : DFA Q Σ)
         ⦃ aug-state : Augmentable Q ⦄
         (input : Set)
         : Set₁
       where
  field
    check : {s : Q}
            → Conf s
            → ℕ
            → Valued input
            → Set
open MessageValidator

-- EasySM characterises augmented automata that can be realised on-chain.
--
-- FIXME: The constraints are not complete yet! We also need to use tick intervals.
--
module EasySM
         (Q : Set) (Σ : Set)
         (dfa : DFA Q Σ)
         {{aug-state : Augmentable Q}}
         {{aug-label : Augmentable Σ}}
         (input  : Set)
         (output : Set)
         (automaton : AugmentedAutomaton Q Σ dfa input output)
         (validator : MessageValidator Q Σ dfa input)
       where

  record TimedConf (s : Q) : Set where
    field
      conf : Conf s
      tick : ℕ

  -- A transition step performs one transition in the automaton and imposes all relevant ledger constrains on it.
  --
  data _∙_⇒[_]_∙_ : {s s' : Q} {l : Σ}
                  → TimedConf s
                  → List (Valued input)
                  → l ⁺
                  → TimedConf s'
                  → List (Valued output)
                  → Set
    where
      ⇒-timed-balanced : {s s' : Q} {l : Σ} {tick tick' : ℕ} {conf : Conf s} {conf' : Conf s'}
                {inbox : List (Valued input)} {inputs : List (Valued input)} {outputs : List (Valued output)} {action : l ⁺} {trans : dfa .δ s l s'}
        → tick < tick'
        → listValue inputs + conf .Conf.value ≡ listValue outputs + conf' .Conf.value
        → automaton .δ⁺ conf inputs action conf' outputs tick' ⦃ trans ⦄
          -------------------------------------------------------------
        → (record { conf = conf; tick = tick } ∙ inputs
          ⇒[ action ]
          record { conf = conf'; tick = tick' } ∙ outputs) -- ⦃ trans ⦄

  -- Message ingress validates an incoming message and adds it to the automata's inbox.
  --
  data _∙_↓[_]_ : {s : Q}
                → TimedConf s
                → List (Valued input)
                → Valued input
                → List (Valued input)
                → Set
    where
      ↓-ingress : {s : Q} {conf : Conf s} {tick : ℕ} {inbox : List (Valued input)} {msg : Valued input}
        → validator .check conf tick msg
          -------------------------------------------------------------
        → record { conf = conf; tick = tick } ∙ inbox
          ↓[ msg ]
          (msg ∷ inbox)

  data Trigger : Set
    where
      step    : {l : Σ} → l ⁺ → Trigger
      ingress : Valued input → Trigger

  data _∙_⇓[_]_∙_ : {s final : Q}
                → TimedConf s
                → List (Valued input)
                → List Trigger
                → TimedConf final
                → List (Valued output)
                → Set
    where
      ⇓-stop : {final : Q} {timedConf : TimedConf final} {tick : ℕ}
        → dfa .F final
          -------------------------------------------------------------
        → timedConf ∙ [] ⇓[ [] ] timedConf ∙ []

      ⇓-step : {s s' final : Q}
          {timedConf : TimedConf s} -- {timedConf' : TimedConf s'}
          {conf' : Conf s'} {tick' : ℕ}
          {finalConf : TimedConf final}
          {l : Σ} {action : l ⁺} {triggers : List Trigger}
          {inputs inbox : List (Valued input)} {newOutputs outputs : List (Valued output)}
        → timedConf ∙ inputs
          ⇒[ action ]
          record { conf = conf'; tick = tick'} ∙ newOutputs
        → record { conf = conf'; tick = tick'} ∙ inbox
          ⇓[ triggers ]
          finalConf ∙ outputs
          -------------------------------------------------------------
        → timedConf ∙ (inputs ++ inbox)
          ⇓[ step action ∷ triggers ]
          finalConf ∙ (newOutputs ++ outputs)

      ⇓-ingress : {s final : Q} {timedConf : TimedConf s} {finalConf : TimedConf final}
          {msg : Valued input} {triggers : List Trigger}
          {inbox inbox' : List (Valued input)} {outputs : List (Valued output)} 
        → timedConf ∙ inbox ↓[ msg ] inbox'
        → timedConf ∙ inbox' ⇓[ triggers ] finalConf ∙ outputs
          -------------------------------------------------------------
        → timedConf ∙ inbox ⇓[ ingress msg ∷ triggers ] finalConf ∙ outputs

  data _⇓[_]_∙_ : {final : Q}
                → TimedConf (dfa .q₀)
                → List Trigger
                → TimedConf final
                → List (Valued output)
                → Set
    where
      ⇓-run : {s final : Q} {timedConf : TimedConf (dfa .q₀)} {finalConf : TimedConf final}
          {triggers : List Trigger} {outputs : List (Valued output)}
        → timedConf ∙ [] ⇓[ triggers ] finalConf ∙ outputs
          -------------------------------------------------------------
        → timedConf ⇓[ triggers ] finalConf ∙ outputs
