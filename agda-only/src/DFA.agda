----------------------------------------------------------------------------------------------------

-- discrete finite automata (DFA)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module DFA where

open import Parser public


----------------------------------------------------------------------------------------------------

module DFAThings where
  record DFA {𝓇 𝓈 𝓁} : Set (lsuc (𝓇 ⊔ 𝓈 ⊔ 𝓁)) where
    constructor mkDFA
    field
      {State}      : Set 𝓈
      {Label}      : Set 𝓁
      initialState : State
      _⇒⟨_⟩_      : State → Label → State → Set 𝓇
      transition   : State → Label → Maybe State
      correctness  : ∀ q l q′ → q ⇒⟨ l ⟩ q′ ⇔ transition q l ≡ just q′

    -- machine that simulates this DFA
    -- NOTE: stops only when invalid transition is attempted
    simMachine : State → ∞Machine Label (Maybe State)
    simMachine q .on l with transition q l
    ... | just q′        = just q′ , just (simMachine q′)
    ... | nothing        = nothing , nothing

  -- textual user interface for DFA
  record TUI-DFA {𝓇 𝓈 𝓁 ℯ} : Set (lsuc (𝓇 ⊔ 𝓈 ⊔ 𝓁 ⊔ ℯ)) where
    constructor mkTUI-DFA
    field
      dfa                : DFA {𝓇} {𝓈} {𝓁}
      {LabelParserErr}   : Set ℯ

    open DFA dfa public

    LabelParser : Set (𝓁 ⊔ ℯ)
    LabelParser = ∞Machine Term (Either LabelParserErr Label)

    field
      showDot            : String
      showState          : State → String
      showLabel          : Label → String
      showLabelParserErr : LabelParserErr → String
      awaitLabel         : LabelParser

    parseLabel : Term → Either LabelParserErr Label
    parseLabel tm = ∞MachineThings.GetEither.step awaitLabel tm

  -- metaprogramming for DFA
  -- TODO: work in progress
  module _ where
    open MetaThings

    -- get state type and label type from transition relation type
    getRelInfo : Name → TC (Name × Name)
    getRelInfo rTpNm = do
        getType rTpNm >>= λ where
          (pi (argv (def qTpNm [])) (abs _
            (pi (argv (def lTpNm [])) (abs _
              (pi (argv (def qTpNm′ [])) (abs _
                (agda-sort (lit 0)))))))) →
                if qTpNm ≟ᴮName qTpNm′
                  then return (qTpNm , lTpNm)
                  else typeError "invalid DFA relation"
          _ →  typeError "invalid DFA relation"

    -- get pre-step state, step label, and post-step state from transition relation constructor
    getStepInfo : Name → TC (Name × Name × Name)
    getStepInfo crNm = do
        getType crNm >>= λ where
          (def _
            ( argv (con qNm₁ [])
            ∷ argv (con lNm [])
            ∷ argv (con qNm₂ []) ∷ [])) →
                return (qNm₁ , lNm , qNm₂)
          _ →  typeError "invalid DFA relation constructor"

    -- derive graphical user interface from transition relation type
    -- TODO: mark initial state
    -- TODO: finish this later
    deriveShowDotFun : Name → Name → TC Unit
    deriveShowDotFun fnNm rTpNm = do
        qTpNm , lTpNm ← getRelInfo rTpNm
        rCrNms ← getCtorNames rTpNm
        rCrStrs ← sequence (map mkCtorStr rCrNms)
        let fnTp = def (quote String) []
        let rStr = String.intersperse "\n"
                     ( ( "digraph {"
                       ∷ "  node [shape = oval];"
                       ∷ "  rankdir = LR;" ∷ [])
                     List′.++ rCrStrs
                     List′.++ ("}" ∷ "" ∷ []))
        let rCrCls = [ clause [] []
                       (def (quote IsString.fromString)
                         ( argh unknown
                         ∷ argh unknown
                         ∷ argv (def (quote Std.isString) [])
                         ∷ argv (lit (string rStr))
                         ∷ argi (con (quote unit) []) ∷ [])) ]
        declareDef (argv fnNm) fnTp
        defineFun fnNm rCrCls
      where
        mkCtorStr : Name → TC String
        mkCtorStr rCrNm = do
            qNm₁ , lNm , qNm₂ ← getStepInfo rCrNm
            qStr₁ ← showName qNm₁
            lStr ← showName lNm
            qStr₂ ← showName qNm₂
            return ("  " ++ qStr₁ ++ " -> " ++ qStr₂ ++ " [ label = \"" ++ lStr ++ "\" ];")

    -- derive transition function from transition relation type
    -- NOTE: will fail if transition relation is not functional
    deriveTransitionFun : Name → Name → TC Unit
    deriveTransitionFun fnNm rTpNm = do
        qTpNm , lTpNm ← getRelInfo rTpNm
        rCrNms ← getCtorNames rTpNm
        rCrCls ← sequence (map mkCtorClause rCrNms)
        *Cls ← mkCatchAllClause
        let fnTp = pi (argv (def qTpNm [])) (abs "q"
                     (pi (argv (def lTpNm [])) (abs "l"
                       (def (quote Maybe)
                         ( argh (def (quote lzero) []) -- TODO: levels
                         ∷ argv (def qTpNm []) ∷ [])))))
        declareDef (argv fnNm) fnTp
        defineFun fnNm (rCrCls List′.++ *Cls)
      where
        mkCtorClause : Name → TC Clause
        mkCtorClause rCrNm = do
            qNm₁ , lNm , qNm₂ ← getStepInfo rCrNm
            return (clause []
                     ( argv (con qNm₁ [])
                     ∷ argv (con lNm []) ∷ [])
                     (con (quote just)
                       ( argh unknown
                       ∷ argh unknown
                       ∷ argv (con qNm₂ []) ∷ [])))

        mkCatchAllClause : TC (List Clause)
        mkCatchAllClause = do
            qTpNm , lTpNm ← getRelInfo rTpNm
            rCrNms ← getCtorNames rTpNm
            qCrNms ← getCtorNames qTpNm
            lCrNms ← getCtorNames lTpNm
            if length rCrNms ≟ᴮNat length qCrNms * length lCrNms
              then return []
              else return [ (clause
                              ( ("_" , argv (def qTpNm []))
                              ∷ ("_" , argv (def lTpNm [])) ∷ [])
                              ( argv (var 1)
                              ∷ argv (var 0) ∷ [])
                              (con (quote nothing)
                                ( argh unknown
                                ∷ argh unknown ∷ []))) ]

    -- derive correctness proof from transition relation type
    -- TODO: should fail if transition relation is not functional
    -- TODO: finish this later
    -- deriveCorrectnessProof : Name → Name → Name → TC Unit
    -- deriveCorrectnessProof pfNm rTpNm fnNm = do
    --     qTpNm , lTpNm ← getRelInfo rTpNm
    --     let pfTp = pi (argv (def qTpNm [])) (abs "q"
    --                  (pi (argv (def lTpNm [])) (abs "l"
    --                    (pi (argv (def qTpNm [])) (abs "q′"
    --                      (def (quote _⇔_)
    --                        ( argh (def (quote lzero) [])
    --                        ∷ argh (def (quote lzero) [])
    --                        ∷ argv (def rTpNm
    --                            ( argv (var 2 [])
    --                            ∷ argv (var 1 [])
    --                            ∷ argv (var 0 []) ∷ []))
    --                        ∷ argv (def (quote _≡_)
    --                            ( argh (def (quote lzero) [])
    --                            ∷ argh (def (quote Maybe)
    --                                ( argh (def (quote lzero) [])
    --                                ∷ argv (def qTpNm []) ∷ []))
    --                            ∷ argv (def fnNm
    --                                ( argv (var 2 [])
    --                                ∷ argv (var 1 []) ∷ []))
    --                            ∷ argv (con (quote just)
    --                                ( argh unknown
    --                                ∷ argh unknown
    --                                ∷ argv (var 0 []) ∷ [])) ∷ [])) ∷ [])))))))
    --     typeError "TODO"

  open DFA public

open DFAThings public using (DFA ; mkDFA ; TUI-DFA ; mkTUI-DFA)


----------------------------------------------------------------------------------------------------
