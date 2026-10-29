----------------------------------------------------------------------------------------------------

-- main coprogram


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Prelude


----------------------------------------------------------------------------------------------------

module Main-ADFA where
  open import ADFA.Multisig

  -- TODO: clean this up
  open TODO

  balance : Value
  balance = 100

  -- run n-of-m multi-signature contract (indexed by DFA)
  open TUIInterpreter-ADFA MultiSig-DFA.tui MultiSig-ADFA.tui balance

  main : Main
  main = StdIO.run handleTUI


----------------------------------------------------------------------------------------------------

module Main where
  open import SADFA.Multisig

  balance : Amount ada
  balance = ada 1000000

  -- run n-of-m multi-signature contract (indexed by DFA)
  open TUIInterpreter-SADFA MultiSig-DFA.tui (MultiSig-SADFA.tui balance)

  -- auction contract (indexed by DFA)
  -- open TUIInterpreter-SADFA Auction-DFA.tui Auction-SADFA.tui

  main : Main
  main = StdIO.run handleTUI


----------------------------------------------------------------------------------------------------
