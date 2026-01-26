----------------------------------------------------------------------------------------------------

-- TODO: clean this up


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module tmp.tmp2 where

-- TODO: clean this up
open import tmp.tmp public


----------------------------------------------------------------------------------------------------

-- TODO: clean this up
module _ where
  -- TODO: token name is currency; token symbol is policy script
  data Currency : Set where
    ada   : Currency
    token : ∀ (nm plc : String) → Currency

  data Amount : Currency → Set where
    ada   : ∀ (n : Nat) → Amount ada
    token : ∀ {nm plc} (n : Nat) → Amount (token nm plc)

  showAmount : ∀ {ccy} → Amount ccy → String
  showAmount (ada n)              = "(ada " ++ showNat n ++ ")"
  showAmount (token {nm} {plc} n) = "(token " ++ nm ++ " " ++ plc ++ " " ++ showNat n ++ ")"

  fromAda : Amount ada → Nat
  fromAda (ada n) = n

  fromToken : ∀ {nm plc} → Amount (token nm plc) → Nat
  fromToken (token n) = n

  record Value : Set where
    constructor $
    field
      {currency} : Currency
      amount     : Amount currency

  pattern $ada n          = $ (ada n)
  pattern $token nm plc n = $ (token {nm} {plc} n)

  -- TODO: datum should be optional
  record UTxO {𝒹} (Datum : Set 𝒹) : Set 𝒹 where
    constructor utxo
    field
      key    : Key
      datum  : Datum
      values : List Value

  open UTxO public


----------------------------------------------------------------------------------------------------
