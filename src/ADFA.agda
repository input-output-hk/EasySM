----------------------------------------------------------------------------------------------------

-- augmented discrete finite automata (ADFA, indexed by DFA)
-- NOTE: states and labels are intended to inherit finiteness guarantees from DFA


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module ADFA where

open import IODFA public

-- TODO: clean this up
open import tmp.tmp public


----------------------------------------------------------------------------------------------------

module ADFAThings where
  record ADFA {°𝓇 °𝓈 °𝓁 𝓇 𝓈 𝓁 𝓍 𝓎} (dfa : DFA {°𝓇} {°𝓈} {°𝓁}) :
      Set (lsuc (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)) where
    constructor mkADFA
    private module ° = DFA dfa
    field
      {State}       : °.State → Set 𝓈
      {Label}       : °.Label → Set 𝓁
      {Input}       : Set 𝓍
      {Output}      : Set 𝓎
      initialState  : State °.initialState

    -- TODO: clean this up
    open TODO public

    Cfg : °.State → Set 𝓈
    Cfg °q = MkCfg (State °q)

    field
      _#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                        Tick → Cfg °q → Label °l → Input →
                        Cfg °q′ → Output → Set 𝓇

    -- transition relation with explicit instance argument
    _⊨_#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                         Tick → Cfg °q → Label °l → Input →
                         Cfg °q′ → Output → Set 𝓇
    _⊨_#_⇒⟨_,_⟩_,_ °r = _#_⇒⟨_,_⟩_,_ {{°r}}

    field
      transition    : ∀ {°q °l} →
                        Tick → Cfg °q → Label °l → Input →
                        Maybe (Σ °.State Cfg × Output)

      correctness   : ∀ {°q °l °q′}
                        t c l x c′ y →
                        Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ t # c ⇒⟨ l , x ⟩ c′ , y) ⇔
                          transition t c l x ≡ just ((°q′ , c′) , y)

    -- NOTE: correctness is formulated specifically so that DFA transition function results can be
    -- recovered from ADFA transition function results
    recover : ∀ {°q °l °q′}
                {t c l x c′ y} →
                transition t c l x ≡ just ((°q′ , c′) , y) →
                  °.transition °q °l ≡ just °q′
    recover eq = °.correctness _ _ _ .fst (correctness _ _ _ _ _ _ .snd eq .fst)

    initialCfg : Value → Cfg °.initialState
    initialCfg v = ⟨ initialState , v ⟩

    -- IODFA that simulates this ADFA
    module _ where
      SimState : °.State → Set 𝓈
      SimState °q = Tick × Cfg °q

      SimLabel : °.Label → Set 𝓁
      SimLabel °l = Label °l

      simInitialState : Value → SimState °.initialState
      simInitialState v = 0 , initialCfg v

      data _ˢ⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                            SimState °q → SimLabel °l → Input →
                            SimState °q′ → Output → Set (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎) where
        sim : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}}
                {t c l x c′ y} →
                t # c ⇒⟨ l , x ⟩ c′ , y →
                (t , c) ˢ⇒⟨ l , x ⟩ (1 + t , c′) , y

      -- simulated transition relation notation with explicit instance argument
      _⊨_ˢ⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                          SimState °q → SimLabel °l → Input →
                          SimState °q′ → Output → Set (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)
      _⊨_ˢ⇒⟨_,_⟩_,_ °r = _ˢ⇒⟨_,_⟩_,_ {{°r}}

      increment : Tick → Σ °.State Cfg × Output → Σ °.State SimState × Output
      increment t ((°q′ , c′) , y) = (°q′ , 1 + t , c′) , y

      simTransition : ∀ {°q °l} →
                        SimState °q → SimLabel °l → Input →
                        Maybe (Σ °.State SimState × Output)
      simTransition (t , c) l x
          = Maybe′.map (increment t) (transition t c l x)

      simCorrectness₁ : ∀ {°q °l °q′}
                          ˢq l x ˢq′ y →
                          Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y) →
                            simTransition ˢq l x ≡ just ((°q′ , ˢq′) , y)
      simCorrectness₁ (t , c) l x (_ , c′) y (°r , sim r)
          = Maybe′.map-just (correctness t c l x c′ y .fst (°r , r))

      simCorrectness₂ : ∀ {°q °l °q′}
                          ˢq l x ˢq′ y →
                          simTransition ˢq l x ≡ just ((°q′ , ˢq′) , y) →
                            Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y)
      simCorrectness₂ (t , c) l x (_ , c′) y eq
        with unmap-just {mx = transition t c l x} eq
      ... | _ , eq′ , refl = let °r , r = correctness t c l x c′ y .snd eq′ in
                               °r , sim {{°r}} r

      simCorrectness : ∀ {°q °l °q′}
                         ˢq l x ˢq′ y →
                         Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y) ⇔
                           simTransition ˢq l x ≡ just ((°q′ , ˢq′) , y)
      simCorrectness ˢq l x ˢq′ y
          = simCorrectness₁ ˢq l x ˢq′ y , simCorrectness₂ ˢq l x ˢq′ y

      simIODFA : Value → IODFA dfa
      simIODFA v = mkIODFA (simInitialState v) _ˢ⇒⟨_,_⟩_,_ simTransition simCorrectness

  -- textual user interface for ADFA
  record TUI-ADFA {°𝓇 °𝓈 °𝓁 °ℯ 𝓇 𝓈 𝓁 𝓍 𝓎 ℯ₁ ℯ₂} (tui : TUI-DFA {°𝓇} {°𝓈} {°𝓁} {°ℯ}) :
      Set (lsuc (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ °ℯ ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎 ⊔ ℯ₁ ⊔ ℯ₂)) where
    constructor mkTUI-ADFA
    private module ° = TUI-DFA tui
    field
      adfa               : ADFA {𝓇 = 𝓇} {𝓈} {𝓁} {𝓍} {𝓎} °.dfa
      {LabelParserErr}   : Set ℯ₁
      {InputParserErr}   : Set ℯ₂

    open ADFA adfa public

    LabelParser : Set (°𝓁 ⊔ 𝓁 ⊔ ℯ₁)
    LabelParser = ∞Machine Term (Either LabelParserErr (Σ °.Label Label))

    InputParser : Set (𝓍 ⊔ ℯ₂)
    InputParser = ∞Machine Term (Either InputParserErr Input)

    field
      showState          : ∀ {°q} → State °q → String
      showLabel          : ∀ {°l} → Label °l → String
      showInput          : Input → String
      showOutput         : Output → String
      showLabelParserErr : LabelParserErr → String
      showInputParserErr : InputParserErr → String
      awaitLabel         : LabelParser
      awaitInput         : InputParser

    showCfg : ∀ {°q} → Cfg °q → String
    showCfg ⟨ q , v ⟩ = "(" ++ showState q ++ " " ++ showNat v ++ ")"

    parseLabel : Term → Either LabelParserErr (Σ °.Label Label)
    parseLabel tm = ∞MachineThings.GetEither.step awaitLabel tm

    parseInput : Term → Either InputParserErr Input
    parseInput tm = ∞MachineThings.GetEither.step awaitInput tm

    -- textual user interface for IODFA that simulates this ADFA
    module _ where
      showSimState : ∀ {°q} → SimState °q → String
      showSimState (t , c) = showNat t ++ " # " ++ showCfg c

      simTUI : Value → TUI-IODFA tui
      simTUI v = mkTUI-IODFA (simIODFA v) showSimState showLabel showInput showOutput
                   showLabelParserErr showInputParserErr awaitLabel awaitInput

  open ADFA public

open ADFAThings public using (ADFA ; mkADFA ; TUI-ADFA ; mkTUI-ADFA)


----------------------------------------------------------------------------------------------------

module _ where
  -- TODO: clean this up
  open TODO

  -- specialized for simulated ADFA
  module TUIInterpreter-ADFA {°𝓇 °ℯ 𝓇} (°tui : TUI-DFA)
      (tui : TUI-ADFA {°𝓇} {°ℯ = °ℯ} {𝓇} °tui) (v : Value) where
    open TUI-ADFA tui
    open TUIInterpreter-IODFA °tui (simTUI v) public


----------------------------------------------------------------------------------------------------
