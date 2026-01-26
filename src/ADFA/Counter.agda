----------------------------------------------------------------------------------------------------

-- counter contract (ADFA version)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module ADFA.Counter where

open import DFA.Counter public
open import ADFA public


----------------------------------------------------------------------------------------------------

module Counter-ADFA where
  private module ° = Counter-DFA

  data State : °.State → Set where
    root : State °.root

  initialState : State °.initialState
  initialState = root

  data Label : °.Label → Set where
    increment : Label °.increment

  Input : Set
  Input = Unit

  Output : Set
  Output = Unit

  -- TODO: clean this up
  open TODO public

  Cfg : °.State → Set
  Cfg °q = MkCfg (State °q)

  data _#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                         Tick → Cfg °q → Label °l → Input →
                         Cfg °q′ → Output → Set where

    increment : ∀ {t count} →
      ----------------------------------------------------------------------------------------
      t # ⟨ root , count ⟩ ⇒⟨ increment , unit ⟩
        ⟨ root , 1 + count ⟩ , unit


  -- transition relation with explicit instance argument
  _⊨_#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                       Tick → Cfg °q → Label °l → Input →
                       Cfg °q′ → Output → Set
  _⊨_#_⇒⟨_,_⟩_,_ °r = _#_⇒⟨_,_⟩_,_ {{°r}}


  transition : ∀ {°q °l} →
                 Tick → Cfg °q → Label °l → Input →
                 Maybe (Σ °.State Cfg × Output)

  transition _ ⟨ root , count ⟩ increment _
      = just ((_ , ⟨ root , 1 + count ⟩) , _)


  correctness : ∀ {°q °l °q′}
                  t c l x c′ y →
                  Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ t # c ⇒⟨ l , x ⟩ c′ , y) ⇔
                    transition t c l x ≡ just ((°q′ , c′) , y)

  correctness _ ⟨ root , count ⟩ increment _ _ _
      = (λ { (_ , increment) → refl }) , λ { refl → _ , increment }


  adfa : ADFA °.dfa
  adfa = mkADFA initialState _#_⇒⟨_,_⟩_,_ transition correctness


----------------------------------------------------------------------------------------------------
