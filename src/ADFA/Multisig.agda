----------------------------------------------------------------------------------------------------

-- n-of-m multi-signature contract (ADFA version, indexed by DFA)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module ADFA.Multisig where

open import DFA.Multisig public
open import ADFA public


----------------------------------------------------------------------------------------------------

module MultiSig-ADFA where
  private module ° = MultiSig-DFA

  -- TODO: clean this up
  open TODO public

  data State : °.State → Set where
    holding    : State °.holding
    collecting : Payment → List Key → State °.collecting

  initialState : State °.initialState
  initialState = holding

  data Label : °.Label → Set where
    propose : Payment → Label °.propose
    add     : Key → Label °.add
    pay     : Label °.pay
    cancel  : Label °.cancel

  Input : Set
  Input = Unit

  Output : Set
  Output = List (Value × Key)

  Cfg : °.State → Set
  Cfg °q = MkCfg (State °q)


  data _#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                         Tick → Cfg °q → Label °l → Input →
                         Cfg °q′ → Output → Set where

    propose : ∀ {t balance payment} →
      payment .deadline > t →
      payment .value < balance →
      ----------------------------------------------------------------------------------------
      t # ⟨ holding , balance ⟩ ⇒⟨ propose payment , unit ⟩
        ⟨ collecting payment [] , balance ⟩ , []

    add : ∀ {t balance key keys payment} →
      isKeyAuth key →
      ----------------------------------------------------------------------------------------
      t # ⟨ collecting payment keys , balance ⟩ ⇒⟨ add key , unit ⟩
        ⟨ collecting payment (key ∷ keys) , balance ⟩ , []

    pay : ∀ {t balance keys payment} →
      t ≤ payment .deadline →
      length keys ≥ reqKeyCount →
      ----------------------------------------------------------------------------------------
      t # ⟨ collecting payment keys , balance ⟩ ⇒⟨ pay , unit ⟩
        ⟨ holding , balance - payment .value ⟩ , [ payment .value , payment .recipient ]

    cancel : ∀ {t balance keys payment} →
      t > payment .deadline →
      ----------------------------------------------------------------------------------------
      t # ⟨ collecting payment keys , balance ⟩ ⇒⟨ cancel , unit ⟩
        ⟨ holding , balance ⟩ , []


  -- transition relation with explicit instance argument
  _⊨_#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                       Tick → Cfg °q → Label °l → Input →
                       Cfg °q′ → Output → Set
  _⊨_#_⇒⟨_,_⟩_,_ °r = _#_⇒⟨_,_⟩_,_ {{°r}}


  transition : ∀ {°q °l} →
                 Tick → Cfg °q → Label °l → Input →
                 Maybe (Σ °.State Cfg × Output)

  transition t ⟨ holding , balance ⟩ (propose payment) _
    with payment .deadline >? t | payment .value <? balance
  ... | yes _ | yes _ = just ((_ , ⟨ collecting payment [] , balance ⟩) , [])
  ... | _     | _     = nothing

  transition _ ⟨ collecting payment keys , balance ⟩ (add key) _
    with isKeyAuth? key
  ... | yes _ = just ((_ , ⟨ collecting payment (key ∷ keys) , balance ⟩) , [])
  ... | _     = nothing

  transition t ⟨ collecting payment keys , balance ⟩ pay _
    with t ≤? payment .deadline | length keys ≥? reqKeyCount
  ... | yes _ | yes _ = just ((_ , ⟨ holding , balance - payment .value ⟩) ,
                          [ payment .value , payment .recipient ])
  ... | _     | _     = nothing

  transition t ⟨ collecting payment keys , balance ⟩ cancel _
    with t >? payment .deadline
  ... | yes _ = just ((_ , ⟨ holding , balance ⟩) , [])
  ... | _     = nothing

  transition _ _ _ _ = nothing


  correctness : ∀ {°q °l °q′}
                  t c l x c′ y →
                  Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ t # c ⇒⟨ l , x ⟩ c′ , y) ⇔
                    transition t c l x ≡ just ((°q′ , c′) , y)

  correctness t ⟨ holding , balance ⟩ (propose payment) _ _ _
    with payment .deadline >? t | payment .value <? balance
  ... | no ¬p₁ | _      = (λ { (_ , propose p₁ _) → p₁ ↯ ¬p₁ }) , λ ()
  ... | yes _  | no ¬p₂ = (λ { (_ , propose _ p₂) → p₂ ↯ ¬p₂ }) , λ ()
  ... | yes p₁ | yes p₂ = (λ { (_ , propose _ _) → refl }) , λ { refl → _ , propose p₁ p₂ }

  correctness _ ⟨ holding , _ ⟩ (add _) _ _ _ = (λ ()) , λ ()
  correctness _ ⟨ holding , _ ⟩ pay     _ _ _ = (λ ()) , λ ()
  correctness _ ⟨ holding , _ ⟩ cancel  _ _ _ = (λ ()) , λ ()

  correctness _ ⟨ collecting _ _ , _ ⟩ (propose _) _ _ _ = (λ ()) , λ ()

  -- NOTE: this case is trivialized by our temporary definition of isKeyAuth
  correctness _ ⟨ collecting _ _ , _ ⟩ (add key) _ _ _
      = (λ { (_ , add key) → refl }) , λ { refl → _ , add _ }

  correctness t ⟨ collecting payment keys , _ ⟩ pay _ _ _
    with t ≤? payment .deadline | length keys ≥? reqKeyCount
  ... | no ¬p₁ | _      = (λ { (_ , pay p₁ _) → p₁ ↯ ¬p₁ }) , λ ()
  ... | yes _  | no ¬p₂ = (λ { (_ , pay _ p₂) → p₂ ↯ ¬p₂ }) , λ ()
  ... | yes p₁ | yes p₂ = (λ { (_ , pay _ _) → refl }) , λ { refl → _ , pay p₁ p₂ }

  correctness t ⟨ collecting payment _ , _ ⟩ cancel _ _ _
    with t >? payment .deadline
  ... | no ¬p = (λ { (_ , cancel p) → p ↯ ¬p }) , λ ()
  ... | yes p = (λ { (_ , cancel _) → refl }) , λ { refl → _ , cancel p }


  adfa : ADFA °.dfa
  adfa = mkADFA initialState _#_⇒⟨_,_⟩_,_ transition correctness

  -- textual user interface for this ADFA
  module _ where
    showState : ∀ {°q} → State °q → String
    showState holding           = "holding"
    showState (collecting p ks) = "(collecting " ++ showPayment p ++ " " ++ showNats ks ++ ")"

    showLabel : ∀ {°l} → Label °l → String
    showLabel (propose p) = "(propose " ++ showPayment p ++ ")"
    showLabel (add k)     = "(add " ++ showNat k ++ ")"
    showLabel pay         = "pay"
    showLabel cancel      = "cancel"

    showInput : Input → String
    showInput unit = "unit"

    showOutput : Output → String
    showOutput y = "(" ++ String.intersperse " " (map aux y) ++ ")"
      where
        aux : Value × Key → String
        aux (v , k) = "(" ++ showNat v ++ " " ++ showNat k ++ ")"

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
    awaitLabel .on (list (atom "propose" ∷ tm ∷ [])) with parsePayment tm
    ... | fail err                                     = fail (badPropose err) , just awaitLabel
    ... | ok p                                         = ok (_ , propose p) , just awaitLabel
    awaitLabel .on (list (atom "add"     ∷ tm ∷ [])) with parseNat tm
    ... | fail err                                     = fail (badAdd err) , just awaitLabel
    ... | ok k                                         = ok (_ , add k) , just awaitLabel
    awaitLabel .on (atom "pay")                      = ok (_ , pay) , just awaitLabel
    awaitLabel .on (atom "cancel")                   = ok (_ , cancel) , just awaitLabel
    awaitLabel .on tm                                = fail (notLabel tm) , just awaitLabel

    InputParser : Set
    InputParser = ∞Machine Term (Either InputParserErr Input)

    awaitInput : InputParser
    awaitInput .on (atom "unit") = ok unit , just awaitInput
    awaitInput .on tm            = fail (notInput tm) , just awaitInput

    tui : TUI-ADFA °.tui
    tui = mkTUI-ADFA adfa showState showLabel showInput showOutput showLabelParserErr
            showInputParserErr awaitLabel awaitInput


----------------------------------------------------------------------------------------------------
