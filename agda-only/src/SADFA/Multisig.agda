----------------------------------------------------------------------------------------------------

-- n-of-m multi-signature contract (SADFA version, indexed by DFA)
-- NOTE: simplified away configurations, replacing them with just states


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module SADFA.Multisig where

open import DFA.Multisig public
open import SADFA public


----------------------------------------------------------------------------------------------------

module MultiSig-SADFA where
  private module ° = MultiSig-DFA

  record Payment : Set where
    constructor payment
    field
      key     : Key
      amount  : Amount ada
      endTime : Tick

  open Payment public

  showPayment : Payment → String
  showPayment p = "(" ++ showKey (p .key) ++ " " ++ showAmount (p .amount) ++ " " ++
                    showTick (p .endTime) ++ ")"

  -- TODO: improve this
  data PaymentParserErr : Set where
    badKey     : NatParserErr → PaymentParserErr
    badAmount  : NatParserErr → PaymentParserErr
    badEndTime : NatParserErr → PaymentParserErr
    notPayment : Term → PaymentParserErr

  showPaymentParserErr : PaymentParserErr → String
  showPaymentParserErr (badKey err)     = "invalid payment key: " ++ showNatParserErr err
  showPaymentParserErr (badAmount err)  = "invalid payment amount: " ++ showNatParserErr err
  showPaymentParserErr (badEndTime err) = "invalid payment end time: " ++ showNatParserErr err
  showPaymentParserErr (notPayment tm)  = "invalid payment '" ++ showTerm tm ++ "'"

  PaymentParser : Set
  PaymentParser = ∞Machine Term (Either PaymentParserErr Payment)

  awaitPayment : PaymentParser
  awaitPayment .on (list [ tm₁ ; tm₂ ; tm₃ ]) with parseNat tm₁ | parseNat tm₂ | parseNat tm₃
  ... | fail err | _        | _                 = fail (badKey err) , just awaitPayment
  ... | ok _     | fail err | _                 = fail (badAmount err) , just awaitPayment
  ... | ok _     | ok _     | fail err          = fail (badEndTime err) , just awaitPayment
  ... | ok k     | ok n     | ok t              = ok (payment k (ada n) t) , just awaitPayment
  awaitPayment .on tm                         = fail (notPayment tm) , just awaitPayment

  parsePayment : Term → Either PaymentParserErr Payment
  parsePayment tm = ∞MachineThings.GetEither.step awaitPayment tm

  data State : °.State → Set where
    holding    : Amount ada → State °.holding
    collecting : Amount ada → Payment → List Key → State °.collecting

  initialState : Amount ada → State °.initialState
  initialState balance = holding balance

  data Label : °.Label → Set where
    propose : Payment → Label °.propose
    add     : Key → Label °.add
    pay     : Label °.pay
    cancel  : Label °.cancel

  Input : Set
  Input = List (UTxO Unit)

  Output : Set
  Output = List (UTxO Unit)

  pattern noDatum = unit


  data _#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                         TickRange → State °q → Label °l → Input →
                         State °q′ → Output → Set where

    propose : ∀ {t blc pmt} →
      pmt .endTime ≥ t .upper →
      fromAda (pmt .amount) < fromAda blc →
      ----------------------------------------------------------------------------------------
      t #
        holding blc ⇒⟨
          propose pmt , [] ⟩
        collecting blc pmt [] , []

    add : ∀ {t blc k ks pmt} →
      isKeyAuth k →
      ----------------------------------------------------------------------------------------
      t #
        collecting blc pmt ks ⇒⟨
          add k , [] ⟩
        collecting blc pmt (k ∷ ks) , []

    pay : ∀ {t blc ks pmt} →
      t .upper ≤ pmt .endTime →
      length ks ≥ reqKeyCount →
      ----------------------------------------------------------------------------------------
      t #
        collecting blc pmt ks ⇒⟨
          pay , [] ⟩
        holding (ada (fromAda blc - fromAda (pmt .amount))) ,
          [ utxo (pmt .key) noDatum [ $ (pmt .amount) ] ]

    cancel : ∀ {t blc ks pmt} →
      t .lower ≥ pmt .endTime →
      ----------------------------------------------------------------------------------------
      t #
        collecting blc pmt ks ⇒⟨
          cancel , [] ⟩
        holding blc , []


  -- transition relation with explicit instance argument
  _⊨_#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                       TickRange → State °q → Label °l → Input →
                       State °q′ → Output → Set
  _⊨_#_⇒⟨_,_⟩_,_ °r = _#_⇒⟨_,_⟩_,_ {{°r}}


  transition : ∀ {°q °l} →
                 TickRange → State °q → Label °l → Input →
                 Maybe (Σ °.State State × Output)

  transition t (holding blc)           (propose pmt) []
    with pmt .endTime ≥? t .upper | fromAda (pmt .amount) <? fromAda blc
  ... | yes _ | yes _ = just ((_ , collecting blc pmt []) , [])
  ... | _     | _     = nothing

  transition _ (collecting blc pmt ks) (add k)       []
    with isKeyAuth? k
  ... | yes _ = just ((_ , collecting blc pmt (k ∷ ks)) , [])
  ... | _     = nothing

  transition t (collecting blc pmt ks) pay           []
    with t .upper ≤? pmt .endTime
      | length ks ≥? reqKeyCount
  ... | yes _ | yes _ = just ((_ , holding (ada (fromAda blc - fromAda (pmt .amount)))) ,
                          [ utxo (pmt .key) noDatum [ $ (pmt .amount) ] ])
  ... | _     | _     = nothing

  transition t (collecting blc pmt ks) cancel        []
    with t .lower ≥? pmt .endTime
  ... | yes _ = just ((_ , holding blc) , [])
  ... | _     = nothing

  transition _ _ _ _ = nothing


  correctness : ∀ {°q °l °q′}
                  t q l x q′ y →
                  Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ t # q ⇒⟨ l , x ⟩ q′ , y) ⇔
                    transition t q l x ≡ just ((°q′ , q′) , y)

  correctness t (holding blc)         (propose pmt) []      _ _
    with pmt .endTime ≥? t .upper | fromAda (pmt .amount) <? fromAda blc
  ... | no ¬c₁ | _      = (λ { (_ , propose c₁ _) → c₁ ↯ ¬c₁ }) , λ ()
  ... | yes _  | no ¬c₂ = (λ { (_ , propose _ c₂) → c₂ ↯ ¬c₂ }) , λ ()
  ... | yes c₁ | yes c₂ = (λ { (_ , propose _ _) → refl }) , λ { refl → _ , propose c₁ c₂ }

  correctness _ (holding _)           (propose _)   (_ ∷ _) _ _ = (λ ()) , λ ()
  correctness _ (holding _)           (add _)       _       _ _ = (λ ()) , λ ()
  correctness _ (holding _)           pay           _       _ _ = (λ ()) , λ ()
  correctness _ (holding _)           cancel        _       _ _ = (λ ()) , λ ()
  correctness _ (collecting _ _ _)    (propose _)   _       _ _ = (λ ()) , λ ()

  -- NOTE: this case is trivialized by our temporary definition of isKeyAuth
  correctness _ (collecting _ _ _)    (add k) []      _ _
    = (λ { (_ , add k) → refl }) , λ { refl → _ , add unit }

  correctness _ (collecting _ _ _)    (add _)       (_ ∷ _) _ _ = (λ ()) , λ ()

  correctness t (collecting _ pmt ks) pay [] _ _
    with t .upper ≤? pmt .endTime | length ks ≥? reqKeyCount
  ... | no ¬c₁ | _      = (λ { (_ , pay c₁ _) → c₁ ↯ ¬c₁ }) , λ ()
  ... | yes _  | no ¬c₂ = (λ { (_ , pay _ c₂) → c₂ ↯ ¬c₂ }) , λ ()
  ... | yes c₁ | yes c₂ = (λ { (_ , pay _ _) → refl }) , λ { refl → _ , pay c₁ c₂ }

  correctness _ (collecting _ _ _)    pay           (_ ∷ _) _ _ = (λ ()) , λ ()

  correctness t (collecting _ pmt _)  cancel [] _ _
    with t .lower ≥? pmt .endTime
  ... | no ¬c = (λ { (_ , cancel c) → c ↯ ¬c }) , λ ()
  ... | yes c = (λ { (_ , cancel _) → refl }) , λ { refl → _ , cancel c }

  correctness _ (collecting _ _ _)    cancel        (_ ∷ _) _ _ = (λ ()) , λ ()


  sadfa : Amount ada → SADFA °.dfa
  sadfa blc = mkSADFA (initialState blc) _#_⇒⟨_,_⟩_,_ transition correctness

  -- textual user interface for this SADFA
  module _ where
    showState : ∀ {°q} → State °q → String
    showState (holding blc)           = "(holding" ++ showAmount blc ++ ")"
    showState (collecting blc pmt ks) = "(collecting " ++ showAmount blc ++ " " ++
                                        showPayment pmt ++ " " ++ showKeys ks ++ ")"

    showLabel : ∀ {°l} → Label °l → String
    showLabel (propose pmt) = "(propose " ++ showPayment pmt ++ ")"
    showLabel (add k)       = "(add " ++ showKey k ++ ")"
    showLabel pay           = "pay"
    showLabel cancel        = "cancel"

    -- TODO: fix this later
    showInput : Input → String
    showInput _ = "TODO"

    -- TODO: fix this later
    showOutput : Output → String
    showOutput _ = "TODO"

    -- TODO: improve this
    data LabelParserErr : Set where
      badPropose : PaymentParserErr → LabelParserErr
      badAdd     : NatParserErr → LabelParserErr
      notLabel   : Term → LabelParserErr

    showLabelParserErr : LabelParserErr → String
    showLabelParserErr (badPropose err) = "invalid 'propose' label: " ++ showPaymentParserErr err
    showLabelParserErr (badAdd err)     = "invalid 'add' label: " ++ showNatParserErr err
    showLabelParserErr (notLabel tm)    = "invalid label '" ++ showTerm tm ++ "'"

    data InputParserErr : Set where
      notInput : Term → InputParserErr

    showInputParserErr : InputParserErr → String
    showInputParserErr (notInput tm) = "invalid input '" ++ showTerm tm ++ "'"

    LabelParser : Set
    LabelParser = ∞Machine Term (Either LabelParserErr (Σ °.Label Label))

    awaitLabel : LabelParser
    awaitLabel .on (list [ atom "propose" ; tm ]) with parsePayment tm
    ... | fail err                                  = fail (badPropose err) , just awaitLabel
    ... | ok p                                      = ok (_ , propose p) , just awaitLabel
    awaitLabel .on (list [ atom "add" ; tm ])     with parseNat tm
    ... | fail err                                   = fail (badAdd err) , just awaitLabel
    ... | ok k                                       = ok (_ , add k) , just awaitLabel
    awaitLabel .on (atom "pay")                    = ok (_ , pay) , just awaitLabel
    awaitLabel .on (atom "cancel")                 = ok (_ , cancel) , just awaitLabel
    awaitLabel .on tm                              = fail (notLabel tm) , just awaitLabel

    InputParser : Set
    InputParser = ∞Machine Term (Either InputParserErr Input)

    awaitInput : InputParser
    awaitInput .on (list []) = ok [] , just awaitInput
    awaitInput .on tm        = fail (notInput tm) , just awaitInput

    tui : Amount ada → TUI-SADFA °.tui
    tui b = mkTUI-SADFA (sadfa b) showState showLabel showInput showOutput showLabelParserErr
              showInputParserErr awaitLabel awaitInput


----------------------------------------------------------------------------------------------------
