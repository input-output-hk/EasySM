----------------------------------------------------------------------------------------------------

-- augmented discrete automata (ADA, not indexed by DFA, unused)
-- NOTE: states and labels are allowed not to be finite
-- see elsewhere for indexed version (ADFA)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module tmp.ADA where

open import IODA public

-- TODO: clean this up
open import tmp.tmp public


----------------------------------------------------------------------------------------------------

module ADAThings where
  record ADA {𝓇 𝓈 𝓁 𝓍 𝓎} : Set (lsuc (𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)) where
    constructor mkADA
    field
      {State}       : Set 𝓈
      {Label}       : Set 𝓁
      {Input}       : Set 𝓍
      {Output}      : Set 𝓎
      initialState  : State

    -- TODO: clean this up
    open TODO public

    Cfg : Set 𝓈
    Cfg = MkCfg State

    field
      _#_⇒⟨_,_⟩_,_ : Tick → Cfg → Label → Input → Cfg → Output → Set 𝓇
      transition    : Tick → Cfg → Label → Input → Maybe (Cfg × Output)
      correctness   : ∀ t c l x c′ y →
                        t # c ⇒⟨ l , x ⟩ c′ , y ⇔ transition t c l x ≡ just (c′ , y)

    initialCfg : Value → Cfg
    initialCfg v = ⟨ initialState , v ⟩

    -- IODA that simulates this ADA
    module _ where
      SimState : Set 𝓈
      SimState = Tick × Cfg

      simInitialState : Value → SimState
      simInitialState v = 0 , initialCfg v

      data _ˢ⇒⟨_,_⟩_,_ : SimState → Label → Input →
                          SimState → Output → Set (𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎) where
        sim : ∀ {t c l x c′ y} →
                t # c ⇒⟨ l , x ⟩ c′ , y →
                (t , c) ˢ⇒⟨ l , x ⟩ (1 + t , c′) , y

      increment : Tick → Cfg × Output → SimState × Output
      increment t (c′ , y) = (1 + t , c′) , y

      simTransition : SimState → Label → Input → Maybe (SimState × Output)
      simTransition (t , c) l x
          = Maybe′.map (increment t) (transition t c l x)

      simCorrectness₁ : ∀ ˢq l x ˢq′ y →
                          ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y → simTransition ˢq l x ≡ just (ˢq′ , y)
      simCorrectness₁ (t , c) l x (_ , c′) y (sim r)
          = Maybe′.map-just (correctness t c l x c′ y .fst r)

      simCorrectness₂ : ∀ ˢq l x ˢq′ y →
                          simTransition ˢq l x ≡ just (ˢq′ , y) → ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y
      simCorrectness₂ (t , c) l x (_ , c′) y eq
        with unmap-just {mx = transition t c l x} eq
      ... | _ , eq′ , refl = sim (correctness t c l x c′ y .snd eq′)

      simCorrectness : ∀ ˢq l x ˢq′ y →
                         ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y ⇔ simTransition ˢq l x ≡ just (ˢq′ , y)
      simCorrectness ˢq l x ˢq′ y
          = simCorrectness₁ ˢq l x ˢq′ y , simCorrectness₂ ˢq l x ˢq′ y

      simIODA : Value → IODA
      simIODA v = mkIODA (simInitialState v) _ˢ⇒⟨_,_⟩_,_ simTransition simCorrectness

  -- textual user interface for ADA
  record TUI-ADA {𝓇 𝓈 𝓁 𝓍 𝓎 ℯ₁ ℯ₂} : Set (lsuc (𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎 ⊔ ℯ₁ ⊔ ℯ₂)) where
    constructor mkTUI-ADA
    field
      ada                : ADA {𝓇} {𝓈} {𝓁} {𝓍} {𝓎}
      {LabelParserErr}   : Set ℯ₁
      {InputParserErr}   : Set ℯ₂

    open ADA ada public

    LabelParser : Set (𝓁 ⊔ ℯ₁)
    LabelParser = ∞Machine Term (Either LabelParserErr Label)

    InputParser : Set (𝓍 ⊔ ℯ₂)
    InputParser = ∞Machine Term (Either InputParserErr Input)

    field
      showDot            : String
      showState          : State → String
      showLabel          : Label → String
      showInput          : Input → String
      showOutput         : Output → String
      showLabelParserErr : LabelParserErr → String
      showInputParserErr : InputParserErr → String
      awaitLabel         : LabelParser
      awaitInput         : InputParser

    showCfg : Cfg → String
    showCfg ⟨ q , v ⟩ = "(" ++ showState q ++ " " ++ showNat v ++ ")"

    parseLabel : Term → Either LabelParserErr Label
    parseLabel tm = ∞MachineThings.GetEither.step awaitLabel tm

    parseInput : Term → Either InputParserErr Input
    parseInput tm = ∞MachineThings.GetEither.step awaitInput tm

    -- textual user interface for IODA that simulates this ADA
    module _ where
      -- TODO: finish this later
      showSimDot : String
      showSimDot = showDot

      showSimState : SimState → String
      showSimState (t , c) = showNat t ++ " # " ++ showCfg c

      simTUI : Value → TUI-IODA
      simTUI v = mkTUI-IODA (simIODA v) showSimDot showSimState showLabel showInput showOutput
                   showLabelParserErr showInputParserErr awaitLabel awaitInput

  open ADA public

open ADAThings public using (ADA ; mkADA ; TUI-ADA ; mkTUI-ADA)


----------------------------------------------------------------------------------------------------

module _ where
  -- TODO: clean this up
  open TODO

  -- specialized for simulated ADA; unused
  module TUIInterpreter-ADA {𝓇} (tui : TUI-ADA {𝓇}) (v : Value) where
    open TUI-ADA tui
    open TUIInterpreter-IODA (simTUI v) public


----------------------------------------------------------------------------------------------------
