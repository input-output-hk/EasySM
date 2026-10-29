----------------------------------------------------------------------------------------------------

-- n-of-m multi-signature contract (DFA version)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module DFA.Multisig where

open import DFA public


----------------------------------------------------------------------------------------------------

module MultiSig-DFA where
  data State : Set where
    holding    : State
    collecting : State

  initialState : State
  initialState = holding

  data Label : Set where
    propose : Label
    add     : Label
    pay     : Label
    cancel  : Label

  data _⇒⟨_⟩_ : State → Label → State → Set where
    instance
      propose : holding    ⇒⟨ propose ⟩ collecting
      add     : collecting ⇒⟨ add ⟩     collecting
      pay     : collecting ⇒⟨ pay ⟩     holding
      cancel  : collecting ⇒⟨ cancel ⟩  holding

  -- transition : State → Label → Maybe State
  -- transition holding    propose = just collecting
  -- transition collecting add     = just collecting
  -- transition collecting pay     = just holding
  -- transition collecting cancel  = just holding
  -- transition _          _       = nothing
  unquoteDecl transition = DFAThings.deriveTransitionFun transition (quote _⇒⟨_⟩_)

  correctness : ∀ q l q′ → q ⇒⟨ l ⟩ q′ ⇔ transition q l ≡ just q′
  correctness holding    propose collecting = (λ { propose → refl }) , λ { refl → propose }
  correctness holding    propose holding    = (λ ()) , λ ()
  correctness holding    add     _          = (λ ()) , λ ()
  correctness holding    pay     _          = (λ ()) , λ ()
  correctness holding    cancel  _          = (λ ()) , λ ()
  correctness collecting add     _          = (λ { add → refl }) , λ { refl → add }
  correctness collecting pay     _          = (λ { pay → refl }) , λ { refl → pay }
  correctness collecting cancel  _          = (λ { cancel → refl }) , λ { refl → cancel }
  correctness collecting propose _          = (λ ()) , λ ()

  dfa : DFA
  dfa = mkDFA initialState _⇒⟨_⟩_ transition correctness

  -- textual user interface for this DFA
  module _ where
--     showDot : String
--     showDot = "digraph {
--   node [shape = oval];
--   rankdir = LR;
--   holding -> collecting [ label = \"propose\" ];
--   collecting -> collecting [ label = \"add\" ];
--   collecting -> holding [ label = \"pay\" ];
--   collecting -> holding [ label = \"cancel\" ];
-- }
-- "
    unquoteDecl showDot = DFAThings.deriveShowDotFun showDot (quote _⇒⟨_⟩_)

    -- showState : State → String
    -- showState holding    = "holding"
    -- showState collecting = "collecting"
    unquoteDecl showState = MetaThings.deriveShowFun showState (quote State)

    -- showLabel : Label → String
    -- showLabel propose = "propose"
    -- showLabel add     = "add"
    -- showLabel pay     = "pay"
    -- showLabel cancel  = "cancel"
    unquoteDecl showLabel = MetaThings.deriveShowFun showLabel (quote Label)

    data LabelParserErr : Set where
      notLabel : Term → LabelParserErr

    showLabelParserErr : LabelParserErr → String
    showLabelParserErr (notLabel tm) = "invalid label '" ++ showTerm tm ++ "'"

    LabelParser : Set
    LabelParser = ∞Machine Term (Either LabelParserErr Label)

    awaitLabel : LabelParser
    awaitLabel .on (atom "propose") = ok propose , just awaitLabel
    awaitLabel .on (atom "add")     = ok add , just awaitLabel
    awaitLabel .on (atom "pay")     = ok pay , just awaitLabel
    awaitLabel .on (atom "cancel")  = ok cancel , just awaitLabel
    awaitLabel .on tm               = fail (notLabel tm) , just awaitLabel

    tui : TUI-DFA
    tui = mkTUI-DFA dfa showDot showState showLabel showLabelParserErr awaitLabel


----------------------------------------------------------------------------------------------------
