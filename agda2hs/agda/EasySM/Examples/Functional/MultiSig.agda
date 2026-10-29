{-# OPTIONS --erasure --no-projection-like #-}

-- Functional version of the MultiSig contract example.
--
module EasySM.Examples.Functional.MultiSig where

open import Haskell.Prelude
open import Haskell.Prim.Maybe                    using (Just; Nothing)
open import Haskell.Prim.Eq                       using (_==_)
open import Haskell.Prim.Ord                      using (_<_; _<=_)

open import EasySM.Functional.DFA
open import EasySM.Functional.Augmented
open DFA
open AugmentedAutomaton


-- Base DFA
--

-- DFA states
--
data State : Type where
  Holding Collecting : State
{-# COMPILE AGDA2HS State #-}

-- DFA labels
--
data Label : Type where
  Propose Add Pay Cancel : Label
{-# COMPILE AGDA2HS Label #-}

-- DFA transition function
--
multiSigTransition : State → Label → Maybe State
multiSigTransition Holding    Propose = Just Collecting
multiSigTransition Collecting Add     = Just Collecting
multiSigTransition Collecting Pay     = Just Holding
multiSigTransition Collecting Cancel  = Just Holding
multiSigTransition _          _       = Nothing
{-# COMPILE AGDA2HS multiSigTransition #-}

multiSigDFA : DFA State Label
multiSigDFA = record
  { transition = multiSigTransition
  ; initial    = Holding
  ; isFinal    = λ where
      Holding    → True
      Collecting → False
  }
{-# COMPILE AGDA2HS multiSigDFA #-}


-- Helper types
--

PayTo : Type
PayTo = Valued KeyHash
{-# COMPILE AGDA2HS PayTo #-}

record Payment : Type where
  no-eta-equality
  constructor MkPayment
  field
    paymentAmount : Value
    receiver : KeyHash
    deadline : Nat
open Payment public
{-# COMPILE AGDA2HS Payment #-}

-- Augmented state type (replaces State⁺ : Pred₀ State)
--
data StatePlus : Type where
  HoldingPlus    : StatePlus
  CollectingPlus : Payment → List KeyHash → StatePlus
{-# COMPILE AGDA2HS StatePlus #-}

-- Augmented label type (replaces Label⁺ : Pred₀ Label)
--
data LabelPlus : Type where
  ProposePlus : Payment → LabelPlus
  AddPlus     : KeyHash → LabelPlus
  PayPlus     : LabelPlus
  CancelPlus  : LabelPlus
{-# COMPILE AGDA2HS LabelPlus #-}


-- Initial configuration
--
initialConf : Value → Conf State StatePlus
initialConf val = MkConf Holding HoldingPlus val
{-# COMPILE AGDA2HS initialConf #-}


-- | Check if a key is authorised. For the engine, we accept all keys.
isAuthorisedKey : KeyHash → Bool
isAuthorisedKey _ = True
{-# COMPILE AGDA2HS isAuthorisedKey #-}

-- | Number of required signatures. For the engine, we require none.
noRequiredSignatures : Nat
noRequiredSignatures = 0
{-# COMPILE AGDA2HS noRequiredSignatures #-}

-- | Truncated subtraction on Nat, via Integer recursion.
-- Avoids pattern matching on Nat constructors (not supported by agda2hs).
{-# TERMINATING #-}
subNat : Nat → Nat → Nat
subNat n m = intToNatLocal (fromNat n - fromNat m)
  where
    intToNatLocal : Integer → Nat
    intToNatLocal i = if i <= 0 then 0 else intToNatLocal (i - 1) + 1
{-# COMPILE AGDA2HS subNat #-}

private variable
  val val' : Value
  payment : Payment
  key : KeyHash
  keys : List KeyHash


-- Augmented transition function
--
multiSigStep : Conf State StatePlus
          → Nat
          → List (Valued ⊤)
          → LabelPlus
          → Maybe (StepResult State StatePlus ⊤ KeyHash)
multiSigStep conf curTick inputs action = go (conf .baseState) (conf .augState) (conf .value) curTick action
  where
    go : State → StatePlus → Value → Nat → LabelPlus → Maybe (StepResult State StatePlus ⊤ KeyHash)

    -- propose: Holding → Collecting
    go Holding HoldingPlus val curTick (ProposePlus payment) =
      if (curTick < payment .deadline) && (payment .paymentAmount < val)
      then Just (MkStepResult
        Collecting
        (MkConf Collecting (CollectingPlus payment []) val)
        []
        (curTick + 1))
      else Nothing
      

    -- add: Collecting → Collecting
    go Collecting (CollectingPlus payment keys) val curTick (AddPlus key) =
      if isAuthorisedKey key
      then Just (MkStepResult
        Collecting
        (MkConf Collecting (CollectingPlus payment (key ∷ keys)) val)
        []
        (curTick + 1))
      else Nothing

    -- pay: Collecting → Holding
    go Collecting (CollectingPlus payment keys) val curTick PayPlus =
      let val' = subNat val (payment .paymentAmount)
      in if (curTick <= payment .deadline) && (noRequiredSignatures <= lengthNatLocal keys) && (val' + payment .paymentAmount == val)
         then Just (MkStepResult
           Holding
           (MkConf Holding HoldingPlus val')
           (MkValued (payment .paymentAmount) (payment .receiver) ∷ [])
           (curTick + 1))
         else Nothing
      where
        _<=?_ = _<=_
        lengthNatLocal : List KeyHash → Nat
        lengthNatLocal [] = 0
        lengthNatLocal (_ ∷ xs) = lengthNatLocal xs + 1

    -- cancel: Collecting → Holding (after deadline)
    go Collecting (CollectingPlus payment keys) val curTick CancelPlus =
      if payment .deadline < curTick
      then Just (MkStepResult
        Holding
        (MkConf Holding HoldingPlus val)
        []
        (curTick + 1))
      else Nothing
      

    -- Invalid combinations
    go _ _ _ _ _ = Nothing
{-# COMPILE AGDA2HS multiSigStep #-}


multiSigAA : AugmentedAutomaton State Label StatePlus LabelPlus ⊤ KeyHash
multiSigAA = record
  { deltaPlus = multiSigStep
  ; q0Plus    = HoldingPlus
  }
{-# COMPILE AGDA2HS multiSigAA #-}
