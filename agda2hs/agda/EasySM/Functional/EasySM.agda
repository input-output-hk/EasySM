{-# OPTIONS --erasure --no-projection-like #-}

-- EasySM (functional style): state machine framework for EUTxO smart contracts.
--
module EasySM.Functional.EasySM where

open import Haskell.Prelude
open import Haskell.Prim.Maybe                    using (Maybe; Just; Nothing)
open import Haskell.Prim.Eq                       using (_==_)
open import Haskell.Prim.Ord                      using (_<_)
open import Haskell.Prim.Tuple                    public

open import EasySM.Functional.DFA
open import EasySM.Functional.Augmented
open DFA
open AugmentedAutomaton


-- Message validator: checks if an incoming message is valid at a given configuration and tick.
--
-- NB: `MessageValidator` is compiled with `existing-class`. The corresponding Haskell
-- type class must be defined on the Haskell side.
--
record MessageValidator
         (q : Type)
         (sPlus : Type)
         (input : Type)
         : Type₁
       where
  no-eta-equality
  constructor MkMessageValidator
  field
    check : Conf q sPlus → Nat → Valued input → Bool
open MessageValidator public
{-# COMPILE AGDA2HS MessageValidator #-}


-- A timed configuration: a configuration plus a clock tick.
--
record TimedConf (q : Type) (aug : Type) : Type where
  no-eta-equality
  constructor MkTimedConf
  field
    conf : Conf q aug
    tick : Nat
open TimedConf public
{-# COMPILE AGDA2HS TimedConf #-}

-- A trigger is either a step (with an augmented label) or an ingress (with a message).
--
data Trigger (lPlus : Type) (input : Type) : Type where
  StepT    : lPlus → Trigger lPlus input
  IngressT : Valued input → Trigger lPlus input
{-# COMPILE AGDA2HS Trigger #-}


-- A trace entry: either the execution of an action or an updated state.
--
-- Tracing is purely observational — it does not affect the behaviour of the automaton.
--
data TraceEntry (q : Type) (sPlus : Type) (lPlus : Type) (input output : Type) : Type where
  -- The execution of a step: the action, its inputs, and its outputs
  StepEntry    : lPlus → List (Valued input) → List (Valued output) → TraceEntry q sPlus lPlus input output
  -- The execution of an ingress: the message
  IngressEntry : Valued input → TraceEntry q sPlus lPlus input output
  -- The updated state: the current timed configuration
  StateEntry   : TimedConf q sPlus → TraceEntry q sPlus lPlus input output
{-# COMPILE AGDA2HS TraceEntry #-}

-- A trace is a list of entries (in chronological order).
--
Trace : Type → Type → Type → Type → Type → Type
Trace q sPlus lPlus input output = List (TraceEntry q sPlus lPlus input output)
{-# COMPILE AGDA2HS Trace #-}


-- EasySM characterises augmented automata that can be realised on-chain.
--
-- FIXME: The constraints are not complete yet! We also need to use tick intervals.
--
module EasySM
         (q : Type) (l : Type)
         (sPlus : Type) (lPlus : Type)
         (input  : Type)
         (output : Type)
         (dfa : DFA q l)
         (automaton : AugmentedAutomaton q l sPlus lPlus input output)
         {{validator : MessageValidator q sPlus input}}
       where

  -- A transition step performs one transition in the automaton and imposes all relevant
  -- ledger constraints on it.
  --
  -- Returns the next timed configuration and the produced outputs, or `Nothing` if the
  -- step is invalid (no transition, time does not progress, or value balance fails).
  --
  step : TimedConf q sPlus
       → List (Valued input)
       → lPlus
       → Maybe (TimedConf q sPlus × List (Valued output))
  step timedConf inputs action = stepWith (automaton .deltaPlus (timedConf .conf) (timedConf .tick) inputs action)
    where
      stepWith : Maybe (StepResult q sPlus input output)
               → Maybe (TimedConf q sPlus × List (Valued output))
      stepWith Nothing = Nothing
      stepWith (Just stepResult) =
        let nextConf = stepResult .StepResult.nextConf
            outputs  = stepResult .StepResult.outputs
            tick'    = stepResult .StepResult.resultTick
            tick     = timedConf .tick
            conf     = timedConf .conf
        in if (tick <? tick') && (listValue inputs + conf .Conf.value == listValue outputs + nextConf .Conf.value)
           then Just (record { conf = nextConf; tick = tick' } , outputs)
           else Nothing
        where
          _<?_ : Nat → Nat → Bool
          _<?_ = _<_

  -- Message ingress validates an incoming message and adds it to the automaton's inbox.
  --
  -- Returns the new inbox, or `Nothing` if the message is invalid.
  --
  ingress : TimedConf q sPlus
          → List (Valued input)
          → Valued input
          → Maybe (List (Valued input))
  ingress timedConf inbox msg =
    if validator .check (timedConf .conf) (timedConf .tick) msg
    then Just (msg ∷ inbox)
    else Nothing

  -- Multi-step execution with tracing: process a list of triggers starting from a timed
  -- configuration, collecting a trace of the execution.
  --
  -- Returns the final timed configuration, the accumulated outputs, and the trace,
  -- or `Nothing` if any step fails or the final state is not accepting.
  --
  multiStepTraced : TimedConf q sPlus
                  → List (Valued input)
                  → List (Trigger lPlus input)
                  → Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
  multiStepTraced timedConf inbox [] =
    if dfa .isFinal (timedConf .conf .Conf.baseState)
    then Just (timedConf , [] , [])
    else Nothing
  multiStepTraced timedConf inbox (StepT action ∷ triggers) =
    multiStepStepTraced (step timedConf inbox action) triggers
    where
      multiStepStepTraced : Maybe (TimedConf q sPlus × List (Valued output))
                          → List (Trigger lPlus input)
                          → Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
      multiStepStepTraced Nothing _ = Nothing
      multiStepStepTraced (Just (timedConf' , outputs)) triggers' =
        multiStepContTraced (multiStepTraced timedConf' [] triggers') outputs
        where
          multiStepContTraced : Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
                              → List (Valued output)
                              → Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
          multiStepContTraced Nothing _ = Nothing
          multiStepContTraced (Just (finalConf , moreOutputs , trace)) outputs' =
            Just (finalConf , outputs' ++ moreOutputs ,
                  (StepEntry action inbox outputs ∷ StateEntry timedConf' ∷ []) ++ trace)
  multiStepTraced timedConf inbox (IngressT msg ∷ triggers) =
    multiStepIngressTraced (ingress timedConf inbox msg) triggers
    where
      multiStepIngressTraced : Maybe (List (Valued input))
                             → List (Trigger lPlus input)
                             → Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
      multiStepIngressTraced Nothing _ = Nothing
      multiStepIngressTraced (Just inbox') triggers' =
        multiStepIngressCont (multiStepTraced timedConf inbox' triggers')
        where
          multiStepIngressCont : Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
                               → Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
          multiStepIngressCont Nothing = Nothing
          multiStepIngressCont (Just (finalConf , outputs , trace)) =
            Just (finalConf , outputs , (IngressEntry msg ∷ StateEntry timedConf ∷ []) ++ trace)

  -- Multi-step execution: process a list of triggers starting from a timed configuration.
  --
  -- Returns the final timed configuration and the accumulated outputs, or `Nothing` if
  -- any step fails or the final state is not accepting.
  --
  multiStep : TimedConf q sPlus
            → List (Valued input)
            → List (Trigger lPlus input)
            → Maybe (TimedConf q sPlus × List (Valued output))
  multiStep timedConf inbox [] =
    if dfa .isFinal (timedConf .conf .Conf.baseState)
    then Just (timedConf , [])
    else Nothing
  multiStep timedConf inbox (StepT action ∷ triggers) =
    multiStepStep (step timedConf inbox action) triggers
    where
      multiStepStep : Maybe (TimedConf q sPlus × List (Valued output))
                    → List (Trigger lPlus input)
                    → Maybe (TimedConf q sPlus × List (Valued output))
      multiStepStep Nothing _ = Nothing
      multiStepStep (Just (timedConf' , outputs)) triggers' =
        multiStepCont (multiStep timedConf' [] triggers') outputs
        where
          multiStepCont : Maybe (TimedConf q sPlus × List (Valued output))
                        → List (Valued output)
                        → Maybe (TimedConf q sPlus × List (Valued output))
          multiStepCont Nothing _ = Nothing
          multiStepCont (Just (finalConf , moreOutputs)) outputs' =
            Just (finalConf , outputs' ++ moreOutputs)
  multiStep timedConf inbox (IngressT msg ∷ triggers) =
    multiStepIngress (ingress timedConf inbox msg) triggers
    where
      multiStepIngress : Maybe (List (Valued input))
                       → List (Trigger lPlus input)
                       → Maybe (TimedConf q sPlus × List (Valued output))
      multiStepIngress Nothing _ = Nothing
      multiStepIngress (Just inbox') triggers' = multiStep timedConf inbox' triggers'

  -- Run the automaton from the initial timed configuration with a list of triggers,
  -- collecting a trace of the execution.
  --
  runTraced : TimedConf q sPlus
            → List (Trigger lPlus input)
            → Maybe (TimedConf q sPlus × List (Valued output) × Trace q sPlus lPlus input output)
  runTraced initialConf triggers = multiStepTraced initialConf [] triggers

  -- Run the automaton from the initial timed configuration with a list of triggers.
  --
  run : TimedConf q sPlus
      → List (Trigger lPlus input)
      → Maybe (TimedConf q sPlus × List (Valued output))
  run initialConf triggers = multiStep initialConf [] triggers

  {-# COMPILE AGDA2HS step #-}
  {-# COMPILE AGDA2HS ingress #-}
  {-# COMPILE AGDA2HS multiStepTraced #-}
  {-# COMPILE AGDA2HS multiStep #-}
  {-# COMPILE AGDA2HS runTraced #-}
  {-# COMPILE AGDA2HS run #-}
