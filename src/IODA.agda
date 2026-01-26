----------------------------------------------------------------------------------------------------

-- discrete automata with I/O (IODA, not indexed by DFA)
-- NOTE: states and labels are allowed not to be finite
-- see elsewhere for indexed version (IODFA)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module IODA where

open import Parser public


----------------------------------------------------------------------------------------------------

module IODAThings where
  record IODA {𝓇 𝓈 𝓁 𝓍 𝓎} : Set (lsuc (𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎)) where
    constructor mkIODA
    field
      {State}      : Set 𝓈
      {Label}      : Set 𝓁
      {Input}      : Set 𝓍
      {Output}     : Set 𝓎
      initialState : State
      _⇒⟨_,_⟩_,_  : State → Label → Input → State → Output → Set 𝓇
      transition   : State → Label → Input → Maybe (State × Output)
      correctness  : ∀ q l x q′ y → q ⇒⟨ l , x ⟩ q′ , y ⇔ transition q l x ≡ just (q′ , y)

    -- machine that simulates this IODA
    -- NOTE: stops only when invalid transition is attempted
    simMachine : State → ∞Machine (Label × Input) (Maybe (State × Output))
    simMachine q .on (l , x) with transition q l x
    ... | just (q′ , y)        = just (q′ , y) , just (simMachine q′)
    ... | nothing              = nothing , nothing

  -- textual user interface for IODA
  record TUI-IODA {𝓇 𝓈 𝓁 𝓍 𝓎 ℯ₁ ℯ₂} : Set (lsuc (𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ 𝓍 ⊔ 𝓎 ⊔ ℯ₁ ⊔ ℯ₂)) where
    constructor mkTUI-IODA
    field
      ioda               : IODA {𝓇} {𝓈} {𝓁} {𝓍} {𝓎}
      {LabelParserErr}   : Set ℯ₁
      {InputParserErr}   : Set ℯ₂

    open IODA ioda public

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

    parseLabel : Term → Either LabelParserErr Label
    parseLabel tm = ∞MachineThings.GetEither.step awaitLabel tm

    parseInput : Term → Either InputParserErr Input
    parseInput tm = ∞MachineThings.GetEither.step awaitInput tm

  open IODA public

open IODAThings public using (IODA ; mkIODA ; TUI-IODA ; mkTUI-IODA)


----------------------------------------------------------------------------------------------------

-- textual user interface interpreter for arbitrary IODA

module TUIInterpreter-IODA {𝓇} (tui : TUI-IODA {𝓇}) where
  open StdIO public using (_>>=_ ; _>>_)
  open TUI-IODA tui

  data Err : Set where
    badTerm       : TermParserErr → Err
    badInput      : InputParserErr → Err
    badLabel      : LabelParserErr → Err
    badCmd        : Term → Err
    badTransition : Err

  showErr : Err → String
  showErr (badTerm err)  = showTermParserErr err
  showErr (badInput err) = showInputParserErr err
  showErr (badLabel err) = showLabelParserErr err
  showErr (badCmd tm)    = "invalid command '" ++ showTerm tm ++ "'"
  showErr badTransition  = "invalid transition"

  data Cmd : Set where
    quit  : Cmd
    reset : Cmd
    put   : Label → Input → Cmd

  readPutCmd : Term → Either Err Cmd
  readPutCmd (list (tm₁ ∷ tm₂ ∷ [])) with parseLabel tm₁ | parseInput tm₂
  ... | fail err | _                   = fail (badLabel err)
  ... | ok _     | fail err            = fail (badInput err)
  ... | ok l     | ok x                = ok (put l x)
  readPutCmd tm                      = fail (badCmd tm)

  readCmd : String → Either Err Cmd
  readCmd str                   with parseTerm (lex str)
  ... | fail err                  = fail (badTerm err)
  ... | ok (atom ":quit"  ∷ [])   = ok quit
  ... | ok (atom ":reset" ∷ [])   = ok reset
  ... | ok (tm            ∷ [])   = readPutCmd tm
  ... | ok tms                    = readPutCmd (list tms)

  data Action : Set where
    prompt : State → Action
    get    : Output → Action
    warn   : Err → Action

  doAction : Action → IO Unit
  doAction (prompt q) = do putStrLn ""
                           putStrLn (showState q)
                           putStr "> "
  doAction (get y)    = putStrLn (showOutput y)
  doAction (warn err) = putStrLn ("error: " ++ showErr err)

  -- de-accumulate
  stringFrom : List Char → String
  stringFrom acc = String.fromList (reverse acc)

  Interpreter : Set
  Interpreter = ∞Machine Char (List Action)

  mutual
    awaitCmd : State → List Char → Interpreter
    awaitCmd q acc .on '\n' with readCmd (stringFrom acc)
    ... | fail err            = continue [ warn err ] q
    ... | ok quit             = [] , nothing
    ... | ok reset            = continue [] initialState
    ... | ok (put l x)        with transition q l x -- NOTE: direct computation here
    ... |   just (q′ , y)       = continue [ get y ] q′
    ... |   nothing             = continue [ warn badTransition ] q
    awaitCmd q acc .on c    = [] , just (awaitCmd q (c ∷ acc))

    continue : List Action → State → List Action × Maybe Interpreter
    continue as q = as List′.++ [ prompt q ] , just (awaitCmd q [])

  handleTUI : IO Polyunit
  handleTUI = do setBuffering stdout noBuffering
                 flush stdout
                 putStrLn showDot
                 cs ← getChars
                 comapM′ (mapM doAction) ([ prompt initialState ] ∷ ♯
                   corun (awaitCmd initialState []) cs)


----------------------------------------------------------------------------------------------------
