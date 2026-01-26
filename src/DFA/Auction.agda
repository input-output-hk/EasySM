----------------------------------------------------------------------------------------------------

-- auction contract (DFA version)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module DFA.Auction where

open import DFA public


----------------------------------------------------------------------------------------------------

module Auction-DFA where
  data State : Set where
    start   : State
    auction : State
    end     : State

  initialState : State
  initialState = start

  data Label : Set where
    deploy : Label
    bid    : Label
    payOut : Label

  data _⇒⟨_⟩_ : State → Label → State → Set where
    instance
      deploy : start   ⇒⟨ deploy ⟩ auction
      bid    : auction ⇒⟨ bid ⟩    auction
      payOut : auction ⇒⟨ payOut ⟩ end

  unquoteDecl transition = DFAThings.deriveTransitionFun transition (quote _⇒⟨_⟩_)

  correctness : ∀ q l q′ → q ⇒⟨ l ⟩ q′ ⇔ transition q l ≡ just q′
  correctness start   deploy start   = (λ ()) , λ ()
  correctness start   deploy auction = (λ { deploy → refl }) , λ { refl → deploy }
  correctness start   deploy end     = (λ ()) , λ ()
  correctness start   bid    _       = (λ ()) , λ ()
  correctness start   payOut _       = (λ ()) , λ ()
  correctness auction deploy _       = (λ ()) , λ ()
  correctness auction bid    start   = (λ ()) , λ ()
  correctness auction bid    auction = (λ { bid → refl }) , λ { refl → bid }
  correctness auction bid    end     = (λ ()) , λ ()
  correctness auction payOut start   = (λ ()) , λ ()
  correctness auction payOut auction = (λ ()) , λ ()
  correctness auction payOut end     = (λ { payOut → refl }) , λ { refl → payOut }
  correctness end     deploy _       = (λ ()) , λ ()
  correctness end     bid    _       = (λ ()) , λ ()
  correctness end     payOut _       = (λ ()) , λ ()

  dfa : DFA
  dfa = mkDFA initialState _⇒⟨_⟩_ transition correctness

  -- textual user interface for this DFA
  module _ where
--     showDot : String
--     showDot = "digraph {
--   node [shape = oval];
--   rankdir = LR;
--   start -> auction [ label = \"deploy\" ];
--   auction -> auction [ label = \"bid\" ];
--   auction -> end [ label = \"payOut\" ];
-- }
-- "
    unquoteDecl showDot = DFAThings.deriveShowDotFun showDot (quote _⇒⟨_⟩_)

    -- showState : State → String
    -- showState start   = "start"
    -- showState auction = "auction"
    -- showState end     = "end"
    unquoteDecl showState = MetaThings.deriveShowFun showState (quote State)

    -- showLabel : Label → String
    -- showLabel deploy = "deploy"
    -- showLabel bid    = "bid"
    -- showLabel payOut = "payOut"
    unquoteDecl showLabel = MetaThings.deriveShowFun showLabel (quote Label)

    data LabelParserErr : Set where
      notLabel : Term → LabelParserErr

    showLabelParserErr : LabelParserErr → String
    showLabelParserErr (notLabel tm) = "invalid label '" ++ showTerm tm ++ "'"

    LabelParser : Set
    LabelParser = ∞Machine Term (Either LabelParserErr Label)

    awaitLabel : LabelParser
    awaitLabel .on (atom "deploy") = ok deploy , just awaitLabel
    awaitLabel .on (atom "bid")    = ok bid , just awaitLabel
    awaitLabel .on (atom "payOut") = ok payOut , just awaitLabel
    awaitLabel .on tm              = fail (notLabel tm) , just awaitLabel

    tui : TUI-DFA
    tui = mkTUI-DFA dfa showDot showState showLabel showLabelParserErr awaitLabel


----------------------------------------------------------------------------------------------------
