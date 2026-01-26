----------------------------------------------------------------------------------------------------

-- simplified augmented discrete finite automata (SADFA, indexed by DFA)
-- NOTE: simplified away configurations, replacing them with just states
-- NOTE: states and labels are intended to inherit finiteness guarantees from DFA


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module SADFA where

open import IODFA public

-- TODO: clean this up
open import tmp.tmp2 public


----------------------------------------------------------------------------------------------------


module SADFAThings where
  record SADFA {°𝓇 °𝓈 °𝓁 𝓇 𝓈 𝓁 𝓍 𝓎} (dfa : DFA {°𝓇} {°𝓈} {°𝓁}) :
      Set (lsuc (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)) where
    constructor mkSADFA
    private module ° = DFA dfa
    field
      {State}       : °.State → Set 𝓈
      {Label}       : °.Label → Set 𝓁
      {Input}       : Set 𝓍
      {Output}      : Set 𝓎
      initialState  : State °.initialState

    field
      _#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                        TickRange → State °q → Label °l → Input →
                        State °q′ → Output → Set 𝓇

    -- transition relation with explicit instance argument
    _⊨_#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                         TickRange → State °q → Label °l → Input →
                         State °q′ → Output → Set 𝓇
    _⊨_#_⇒⟨_,_⟩_,_ °r = _#_⇒⟨_,_⟩_,_ {{°r}}

    field
      transition    : ∀ {°q °l} →
                        TickRange → State °q → Label °l → Input →
                        Maybe (Σ °.State State × Output)

      correctness   : ∀ {°q °l °q′}
                        t q l x q′ y →
                        Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ t # q ⇒⟨ l , x ⟩ q′ , y) ⇔
                          transition t q l x ≡ just ((°q′ , q′) , y)

    -- NOTE: correctness is formulated specifically so that DFA transition function results can be
    -- recovered from SADFA transition function results
    recover : ∀ {°q °l °q′}
                {t q l x q′ y} →
                transition t q l x ≡ just ((°q′ , q′) , y) →
                  °.transition °q °l ≡ just °q′
    recover eq = °.correctness _ _ _ .fst (correctness _ _ _ _ _ _ .snd eq .fst)

    -- IODFA that simulates this SADFA
    module _ where
      SimState : °.State → Set 𝓈
      SimState °q = TickRange × State °q

      SimLabel : °.Label → Set 𝓁
      SimLabel °l = Label °l

      initialSimState : SimState °.initialState
      initialSimState = initialTickRange , initialState

      nextSimState : TickRange → Σ °.State State × Output → Σ °.State SimState × Output
      nextSimState t ((°q′ , q′) , y) = (°q′ , nextTickRange t , q′) , y

      data _ˢ⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                            SimState °q → SimLabel °l → Input →
                            SimState °q′ → Output → Set (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎) where
        sim : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}}
                {t q l x q′ y} →
                t # q ⇒⟨ l , x ⟩ q′ , y →
                (t , q) ˢ⇒⟨ l , x ⟩ (nextTickRange t , q′) , y

      -- simulated transition relation notation with explicit instance argument
      _⊨_ˢ⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                          SimState °q → SimLabel °l → Input →
                          SimState °q′ → Output → Set (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)
      _⊨_ˢ⇒⟨_,_⟩_,_ °r = _ˢ⇒⟨_,_⟩_,_ {{°r}}

      simTransition : ∀ {°q °l} →
                        SimState °q → SimLabel °l → Input →
                        Maybe (Σ °.State SimState × Output)
      simTransition (t , q) l x
          = Maybe′.map (nextSimState t) (transition t q l x)

      simCorrectness₁ : ∀ {°q °l °q′}
                          ˢq l x ˢq′ y →
                          Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y) →
                            simTransition ˢq l x ≡ just ((°q′ , ˢq′) , y)
      simCorrectness₁ (t , q) l x (_ , q′) y (°r , sim r)
          = Maybe′.map-just (correctness t q l x q′ y .fst (°r , r))

      simCorrectness₂ : ∀ {°q °l °q′}
                          ˢq l x ˢq′ y →
                          simTransition ˢq l x ≡ just ((°q′ , ˢq′) , y) →
                            Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y)
      simCorrectness₂ (t , q) l x (_ , q′) y eq
        with unmap-just {mx = transition t q l x} eq
      ... | _ , eq′ , refl = let °r , r = correctness t q l x q′ y .snd eq′ in
                               °r , sim {{°r}} r

      simCorrectness : ∀ {°q °l °q′}
                         ˢq l x ˢq′ y →
                         Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ ˢq ˢ⇒⟨ l , x ⟩ ˢq′ , y) ⇔
                           simTransition ˢq l x ≡ just ((°q′ , ˢq′) , y)
      simCorrectness ˢq l x ˢq′ y
          = simCorrectness₁ ˢq l x ˢq′ y , simCorrectness₂ ˢq l x ˢq′ y

      simIODFA : IODFA dfa
      simIODFA = mkIODFA initialSimState _ˢ⇒⟨_,_⟩_,_ simTransition simCorrectness

  -- textual user interface for SADFA
  record TUI-SADFA {°𝓇 °𝓈 °𝓁 °ℯ 𝓇 𝓈 𝓁 𝓍 𝓎 ℯ₁ ℯ₂} (tui : TUI-DFA {°𝓇} {°𝓈} {°𝓁} {°ℯ}) :
      Set (lsuc (°𝓇 ⊔ °𝓈 ⊔ °𝓁 ⊔ °ℯ ⊔ 𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎 ⊔ ℯ₁ ⊔ ℯ₂)) where
    constructor mkTUI-SADFA
    private module ° = TUI-DFA tui
    field
      sadfa              : SADFA {𝓇 = 𝓇} {𝓈} {𝓁} {𝓍} {𝓎} °.dfa
      {LabelParserErr}   : Set ℯ₁
      {InputParserErr}   : Set ℯ₂

    open SADFA sadfa public

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

    -- textual user interface for IODFA that simulates this SADFA
    module _ where
      showSimState : ∀ {°q} → SimState °q → String
      showSimState (t , q) = showTickRange t ++ " # " ++ showState q

      simTUI : TUI-IODFA tui
      simTUI = mkTUI-IODFA simIODFA showSimState showLabel showInput showOutput
                 showLabelParserErr showInputParserErr awaitLabel awaitInput

  open SADFA public

open SADFAThings public using (SADFA ; mkSADFA ; TUI-SADFA ; mkTUI-SADFA)


----------------------------------------------------------------------------------------------------

-- specialized for simulated SADFA
module TUIInterpreter-SADFA {°𝓇 °ℯ 𝓇} (°tui : TUI-DFA)
    (tui : TUI-SADFA {°𝓇} {°ℯ = °ℯ} {𝓇} °tui) where
  open TUI-SADFA tui
  open TUIInterpreter-IODFA °tui simTUI public


----------------------------------------------------------------------------------------------------
