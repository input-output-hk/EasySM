----------------------------------------------------------------------------------------------------

-- TODO: clean this up


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module tmp.tmp where

open import Parser public


----------------------------------------------------------------------------------------------------

module _ where
  -- TODO: improve this
  Key : Set
  Key = Nat

  _≟ᴮKey_ : Key → Key → Bool
  k₁ ≟ᴮKey k₂ = k₁ ≟ᴮNat k₂

  showKey : Key → String
  showKey k = showNat k

  showKeys : List Key → String
  showKeys ks = showNats ks

  isKeyAuth : Key → Set
  isKeyAuth _ = Unit

  isKeyAuth? : ∀ k → Dec (isKeyAuth k)
  isKeyAuth? k = yes _

  reqKeyCount : Nat
  reqKeyCount = 1

  -- TODO: improve this
  Tick = Nat

  showTick : Tick → String
  showTick t = showNat t

  -- TODO: make tick ranges inclusive or exclusive at both ends, or infinity
  -- NOTE: currently assuming [lower, upper) following JF's analysis
  record TickRange : Set where
    constructor _,_
    field
      lower : Tick
      upper : Tick

  open TickRange public

  initialTickRange : TickRange
  initialTickRange = 0 , 1

  nextTickRange : TickRange → TickRange
  nextTickRange t = 1 + t .lower , 1 + t .upper

  showTickRange : TickRange → String
  showTickRange t = "[" ++ showTick (t .lower) ++ "," ++ showTick (t .upper) ++ ")"


-- TODO: clean this up
module TODO where
  Value : Set
  Value = Nat

  record MkCfg {𝓈} (State : Set 𝓈) : Set 𝓈 where
    constructor ⟨_,_⟩
    field
      state : State
      value : Value

  open MkCfg public

  record Payment : Set where
    constructor mkPayment
    field
      value     : Value
      recipient : Key
      deadline  : Tick

  open Payment public

  showPayment : Payment → String
  showPayment p = "(" ++ showNat (p .value) ++ " " ++ showNat (p .recipient) ++ " " ++
                    showNat (p .deadline) ++ ")"

  data PaymentParserErr : Set where
    badValue     : NatParserErr → PaymentParserErr
    badRecipient : NatParserErr → PaymentParserErr
    badDeadline  : NatParserErr → PaymentParserErr
    notPayment   : Term → PaymentParserErr

  showPaymentParserErr : PaymentParserErr → String
  showPaymentParserErr (badValue err)     = "invalid payment value: " ++ showNatParserErr err
  showPaymentParserErr (badRecipient err) = "invalid payment recipient: " ++ showNatParserErr err
  showPaymentParserErr (badDeadline err)  = "invalid payment deadline: " ++ showNatParserErr err
  showPaymentParserErr (notPayment tm)    = "invalid payment '" ++ showTerm tm ++ "'"

  PaymentParser : Set
  PaymentParser = ∞Machine Term (Either PaymentParserErr Payment)

  awaitPayment : PaymentParser
  awaitPayment .on (list (tm₁ ∷ tm₂ ∷ tm₃ ∷ [])) with parseNat tm₁ | parseNat tm₂ | parseNat tm₃
  ... | fail err | _        | _                    = fail (badValue err) , just awaitPayment
  ... | ok _     | fail err | _                    = fail (badRecipient err) , just awaitPayment
  ... | ok _     | ok _     | fail err             = fail (badDeadline err) , just awaitPayment
  ... | ok v     | ok r     | ok d                 = ok (mkPayment v r d) , just awaitPayment
  awaitPayment .on tm                            = fail (notPayment tm) , just awaitPayment

  parsePayment : Term → Either PaymentParserErr Payment
  parsePayment tm = ∞MachineThings.GetEither.step awaitPayment tm


----------------------------------------------------------------------------------------------------
