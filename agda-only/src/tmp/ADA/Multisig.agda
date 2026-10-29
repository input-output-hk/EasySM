----------------------------------------------------------------------------------------------------

-- n-of-m multi-signature contract (ADA version, not indexed by DFA, unused)
-- see elsewhere for indexed version (MultiSig-ADFA)


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module tmp.ADA.Multisig where

open import DFA.Multisig public
open import tmp.ADA public


----------------------------------------------------------------------------------------------------

module MultiSig-ADA where
  -- TODO: clean this up
  open TODO public

  data State : Set where
    holding    : State
    collecting : Payment → List Key → State

  initialState : State
  initialState = holding

  data Label : Set where
    propose : Payment → Label
    add     : Key → Label
    pay     : Label
    cancel  : Label

  Input : Set
  Input = Unit

  Output : Set
  Output = List (Value × Key)

  Cfg : Set
  Cfg = MkCfg State


  data _#_⇒⟨_,_⟩_,_ : Tick → Cfg → Label → Input → Cfg → Output → Set where

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


  transition : Tick → Cfg → Label → Input → Maybe (Cfg × Output)

  transition t ⟨ holding , balance ⟩ (propose payment) _
    with payment .deadline >? t | payment .value <? balance
  ... | yes _ | yes _ = just (⟨ collecting payment [] , balance ⟩ , [])
  ... | _     | _     = nothing

  transition _ ⟨ collecting payment keys , balance ⟩ (add key) _
    with isKeyAuth? key
  ... | yes _ = just (⟨ collecting payment (key ∷ keys) , balance ⟩ , [])
  ... | _     = nothing

  transition t ⟨ collecting payment keys , balance ⟩ pay _
    with t ≤? payment .deadline | length keys ≥? reqKeyCount
  ... | yes _ | yes _ = just (⟨ holding , balance - payment .value ⟩ ,
                          [ payment .value , payment .recipient ])
  ... | _     | _     = nothing

  transition t ⟨ collecting payment keys , balance ⟩ cancel _
    with t >? payment .deadline
  ... | yes _ = just (⟨ holding , balance ⟩ , [])
  ... | _     = nothing

  transition _ _ _ _ = nothing


  correctness : ∀ t c l x c′ y → t # c ⇒⟨ l , x ⟩ c′ , y ⇔ transition t c l x ≡ just (c′ , y)

  correctness t ⟨ holding , balance ⟩ (propose payment) _ _ _
    with payment .deadline >? t | payment .value <? balance
  ... | no ¬p₁ | _      = (λ { (propose p₁ _) → p₁ ↯ ¬p₁ }) , λ ()
  ... | yes _  | no ¬p₂ = (λ { (propose _ p₂) → p₂ ↯ ¬p₂ }) , λ ()
  ... | yes p₁ | yes p₂ = (λ { (propose _ _) → refl }) , λ { refl → propose p₁ p₂ }

  correctness _ ⟨ holding , _ ⟩ (add _) _ _ _ = (λ ()) , λ ()
  correctness _ ⟨ holding , _ ⟩ pay     _ _ _ = (λ ()) , λ ()
  correctness _ ⟨ holding , _ ⟩ cancel  _ _ _ = (λ ()) , λ ()

  correctness _ ⟨ collecting _ _ , _ ⟩ (propose _) _ _ _ = (λ ()) , λ ()

  -- NOTE: this case is trivialized by our temporary definition of isKeyAuth
  correctness _ ⟨ collecting _ _ , _ ⟩ (add key) _ _ _
      = (λ { (add key) → refl }) , λ { refl → add _ }

  correctness t ⟨ collecting payment keys , _ ⟩ pay _ _ _
    with t ≤? payment .deadline | length keys ≥? reqKeyCount
  ... | no ¬p₁ | _      = (λ { (pay p₁ _) → p₁ ↯ ¬p₁ }) , λ ()
  ... | yes _  | no ¬p₂ = (λ { (pay _ p₂) → p₂ ↯ ¬p₂ }) , λ ()
  ... | yes p₁ | yes p₂ = (λ { (pay _ _) → refl }) , λ { refl → pay p₁ p₂ }

  correctness t ⟨ collecting payment _ , _ ⟩ cancel _ _ _
    with t >? payment .deadline
  ... | no ¬p = (λ { (cancel p) → p ↯ ¬p }) , λ ()
  ... | yes p = (λ { (cancel _) → refl }) , λ { refl → cancel p }


  ada : ADA
  ada = mkADA initialState _#_⇒⟨_,_⟩_,_ transition correctness

  -- textual user interface for this ADA
  module _ where
    showDot : String
    showDot = "digraph {
  node [shape = oval];
  rankdir = LR;
  holding -> collecting [ label = \"propose\" ];
  collecting -> collecting [ label = \"add\" ];
  collecting -> holding [ label = \"pay\" ];
  collecting -> holding [ label = \"cancel\" ];
}
"

    showState : State → String
    showState holding           = "holding"
    showState (collecting p ks) = "(collecting " ++ showPayment p ++ " " ++ showNats ks ++ ")"

    showLabel : Label → String
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
    LabelParser = ∞Machine Term (Either LabelParserErr Label)

    awaitLabel : LabelParser
    awaitLabel .on (list (atom "propose" ∷ tm ∷ [])) with parsePayment tm
    ... | fail err                                     = fail (badPropose err) , just awaitLabel
    ... | ok p                                         = ok (propose p) , just awaitLabel
    awaitLabel .on (list (atom "add"     ∷ tm ∷ [])) with parseNat tm
    ... | fail err                                     = fail (badAdd err) , just awaitLabel
    ... | ok k                                         = ok (add k) , just awaitLabel
    awaitLabel .on (atom "pay")                      = ok pay , just awaitLabel
    awaitLabel .on (atom "cancel")                   = ok cancel , just awaitLabel
    awaitLabel .on tm                                = fail (notLabel tm) , just awaitLabel

    InputParser : Set
    InputParser = ∞Machine Term (Either InputParserErr Input)

    awaitInput : InputParser
    awaitInput .on (atom "unit") = ok unit , just awaitInput
    awaitInput .on tm            = fail (notInput tm) , just awaitInput

    tui : TUI-ADA
    tui = mkTUI-ADA ada showDot showState showLabel showInput showOutput showLabelParserErr
            showInputParserErr awaitLabel awaitInput


----------------------------------------------------------------------------------------------------
