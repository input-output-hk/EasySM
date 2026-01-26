----------------------------------------------------------------------------------------------------

-- discrete finite automata with I/O (IODFA, indexed by DFA)
-- NOTE: states and labels are intended to inherit finiteness guarantees from DFA


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module IODFA where

open import DFA as DFA′ public
open import IODA public


----------------------------------------------------------------------------------------------------

module IODFAThings where
  record IODFA {°𝓇 °𝓈 °𝓁 𝓇 𝓈 𝓁 𝓍 𝓎} (dfa : DFA {°𝓇} {°𝓈} {°𝓁}) :
      Set (lsuc (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)) where
    constructor mkIODFA
    private module ° = DFA dfa
    field
      {State}      : °.State → Set 𝓈
      {Label}      : °.Label → Set 𝓁
      {Input}      : Set 𝓍
      {Output}     : Set 𝓎
      initialState : State °.initialState

      _⇒⟨_,_⟩_,_  : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                       State °q → Label °l → Input →
                       State °q′ → Output → Set 𝓇

    -- transition relation with explicit instance argument
    _⊨_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                       State °q → Label °l → Input →
                       State °q′ → Output → Set 𝓇
    _⊨_⇒⟨_,_⟩_,_ °r = _⇒⟨_,_⟩_,_ {{°r}}

    field
      transition   : ∀ {°q °l} →
                       State °q → Label °l → Input →
                       Maybe (Σ °.State State × Output)

      correctness  : ∀ {°q °l °q′}
                       q l x q′ y →
                       Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ q ⇒⟨ l , x ⟩ q′ , y) ⇔
                         transition q l x ≡ just ((°q′ , q′) , y)

    -- NOTE: correctness is formulated specifically so that DFA transition function results can be
    -- recovered from IODFA transition function results
    recover : ∀ {°q °l °q′}
                {q l x q′ y} →
                transition q l x ≡ just ((°q′ , q′) , y) →
                  °.transition °q °l ≡ just °q′
    recover eq = °.correctness _ _ _ .fst (correctness _ _ _ _ _ .snd eq .fst)

    -- machine that simulates this IODFA
    -- NOTE: stops only when invalid transition is attempted
    simMachine : ∀ {°q °l} →
                   State °q → ∞Machine (Label °l × Input) (Maybe (Σ °.State State × Output))
    simMachine q .on (l , x)    with transition q l x
    ... | just ((°q′ , q′) , y)   = just ((°q′ , q′) , y) , just (simMachine q′)
    ... | nothing                 = nothing , nothing

    -- IODA that simulates this IODFA
    module _ where
      SimState : Set (°𝓈 ⊔ 𝓈)
      SimState = Σ °.State State

      SimLabel : Set (°𝓁 ⊔ 𝓁)
      SimLabel = Σ °.Label Label

      simInitialState : SimState
      simInitialState = °.initialState , initialState

      data _ˢ⇒⟨_,_⟩_,_ : SimState → SimLabel → Input →
                          SimState → Output → Set (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎) where
        sim : ∀ {°q °l °q′}
                {q l x q′ y} →
                Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ q ⇒⟨ l , x ⟩ q′ , y) →
                  (°q , q) ˢ⇒⟨ (°l , l) , x ⟩ (°q′ , q′) , y

      simTransition : SimState → SimLabel → Input → Maybe (SimState × Output)
      simTransition (_ , q) (_ , l) x
          = transition q l x

      simCorrectness₁ : ∀ ˢq ˢl x ˢq′ y →
                          ˢq ˢ⇒⟨ ˢl , x ⟩ ˢq′ , y → simTransition ˢq ˢl x ≡ just (ˢq′ , y)
      simCorrectness₁ (_ , q) (_ , l) x (_ , q′) y (sim r)
          = correctness q l x q′ y .fst r

      simCorrectness₂ : ∀ ˢq ˢl x ˢq′ y →
                          simTransition ˢq ˢl x ≡ just (ˢq′ , y) → ˢq ˢ⇒⟨ ˢl , x ⟩ ˢq′ , y
      simCorrectness₂ (_ , q) (_ , l) x (_ , q′) y eq
          = sim (correctness q l x q′ y .snd eq)

      simCorrectness : ∀ ˢq ˢl x ˢq′ y →
                         ˢq ˢ⇒⟨ ˢl , x ⟩ ˢq′ , y ⇔ simTransition ˢq ˢl x ≡ just (ˢq′ , y)
      simCorrectness ˢq ˢl x ˢq′ y
          = simCorrectness₁ ˢq ˢl x ˢq′ y , simCorrectness₂ ˢq ˢl x ˢq′ y

      simIODA : IODA
      simIODA = mkIODA simInitialState _ˢ⇒⟨_,_⟩_,_ simTransition simCorrectness

  -- textual user interface for IODFA
  record TUI-IODFA {°𝓇 °𝓈 °𝓁 °ℯ 𝓇 𝓈 𝓁 𝓍 𝓎 ℯ₁ ℯ₂} (tui : TUI-DFA {°𝓇} {°𝓈} {°𝓁} {°ℯ}) :
      Set (lsuc (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ °ℯ ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎 ⊔ ℯ₁ ⊔ ℯ₂)) where
    constructor mkTUI-IODFA
    private module ° = TUI-DFA tui
    field
      iodfa              : IODFA {𝓇 = 𝓇} {𝓈} {𝓁} {𝓍} {𝓎} °.dfa
      {LabelParserErr}   : Set ℯ₁
      {InputParserErr}   : Set ℯ₂

    open IODFA iodfa public

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

    parseLabel : Term → Either LabelParserErr (Σ °.Label Label)
    parseLabel tm = ∞MachineThings.GetEither.step awaitLabel tm

    parseInput : Term → Either InputParserErr Input
    parseInput tm = ∞MachineThings.GetEither.step awaitInput tm

    -- textual user interface for IODA that simulates this IODFA
    module _ where
      -- TODO: finish this later
      showSimDot : String
      showSimDot = °.showDot

      showSimState : SimState → String
      showSimState (_ , q) = showState q

      showSimLabel : SimLabel → String
      showSimLabel (_ , l) = showLabel l

      simTUI : TUI-IODA
      simTUI = mkTUI-IODA simIODA showSimDot showSimState showSimLabel showInput showOutput
                 showLabelParserErr showInputParserErr awaitLabel awaitInput

  open IODFA public

open IODFAThings public using (IODFA ; mkIODFA ; TUI-IODFA ; mkTUI-IODFA)


----------------------------------------------------------------------------------------------------

module _ where
  -- specialized for simulated IODFA
  module TUIInterpreter-IODFA {°𝓇 °ℯ 𝓇} (°tui : TUI-DFA)
      (tui : TUI-IODFA {°𝓇} {°ℯ = °ℯ} {𝓇} °tui) where
    open TUI-IODFA tui
    open TUIInterpreter-IODA simTUI public


----------------------------------------------------------------------------------------------------
