----------------------------------------------------------------------------------------------------

-- counter contract (DFA version)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module DFA.Counter where

open import DFA public


----------------------------------------------------------------------------------------------------

module Counter-DFA where
  data State : Set where
    root : State

  initialState : State
  initialState = root

  data Label : Set where
    increment : Label

  data _⇒⟨_⟩_ : State → Label → State → Set where
    instance
      increment : root ⇒⟨ increment ⟩ root

  -- transition : State → Label → Maybe State
  -- transition root increment = just root
  unquoteDecl transition = DFAThings.deriveTransitionFun transition (quote _⇒⟨_⟩_)

  correctness : ∀ q l q′ → q ⇒⟨ l ⟩ q′ ⇔ transition q l ≡ just q′
  correctness root increment root = (λ { increment → refl }) , λ { refl → increment }

  dfa : DFA
  dfa = mkDFA initialState _⇒⟨_⟩_ transition correctness

  -- textual user interface for this DFA
  module _ where
--     showDot : String
--     showDot = "digraph {
--   node [shape = oval];
--   rankdir = LR;
--   root -> root [ label = \"increment\" ];
-- }
-- "
    unquoteDecl showDot = DFAThings.deriveShowDotFun showDot (quote _⇒⟨_⟩_)

    -- showState : State → String
    -- showState root = "root"
    unquoteDecl showState = MetaThings.deriveShowFun showState (quote State)

    -- showLabel : Label → String
    -- showLabel increment = "increment"
    unquoteDecl showLabel = MetaThings.deriveShowFun showLabel (quote Label)

    data LabelParserErr : Set where
      notLabel : Term → LabelParserErr

    showLabelParserErr : LabelParserErr → String
    showLabelParserErr (notLabel tm) = "invalid label '" ++ showTerm tm ++ "'"

    LabelParser : Set
    LabelParser = ∞Machine Term (Either LabelParserErr Label)

    awaitLabel : LabelParser
    awaitLabel .on (atom "increment") = ok increment , just awaitLabel
    awaitLabel .on tm                 = fail (notLabel tm) , just awaitLabel

    tui : TUI-DFA
    tui = mkTUI-DFA dfa showDot showState showLabel showLabelParserErr awaitLabel


----------------------------------------------------------------------------------------------------
