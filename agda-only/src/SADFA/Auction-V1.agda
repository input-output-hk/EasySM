----------------------------------------------------------------------------------------------------

-- auction contract (SADFA version, indexed by DFA)
-- NOTE: first draft with comments based on SC group feedback


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module SADFA.Auction-V1 where

open import DFA.Auction public
open import SADFA public


----------------------------------------------------------------------------------------------------

module Auction-SADFA where
  private module ° = Auction-DFA

  -- NOTE: ignoring bid address field
  record Bid : Set where
    constructor bid
    field
      key    : Key
      amount : Amount ada

  open Bid public

  -- NOTE: state is supposed to be represented on chain as datum in contract's UTxO
  -- TODO: should state include highestBid, since it already must be included in auction datum?
  --       (ask Manuel)
  data State : °.State → Set where
    start   : ∀ (auctionRefKey auctionKey : Key) → State °.start
    auction : ∀ (auctionKey : Key) (endTime : Tick) (tokenNm tokenPlc : String)
                (minBidAmt : Amount ada) (origSeller : Key) (highestBid : Maybe Bid) →
                State °.auction
    end     : State °.end

  initialState : Key → Key → State °.initialState
  initialState auctionRefKey auctionKey = start auctionRefKey auctionKey

  data Label : °.Label → Set where
    deploy : ∀ (endTime : Tick) (tokenNm tokenPlc : String) (minBid : Amount ada) → Label °.deploy
    bid    : ∀ (newBid : Bid) → Label °.bid
    payOut : Label °.payOut

  Input : Set
  Input = List (UTxO (Either Unit (Maybe Bid)))

  -- TODO: stop tracking fees? (ask Manuel) aha! answered below
  record Output : Set where
    constructor _,_
    field
      utxos : List (UTxO (Either Unit (Maybe Bid)))
      fee   : Amount ada

  pattern noDatum    = left unit
  pattern noBidDatum = right nothing
  pattern bidDatum b = right (just b)

  -- TODO: we can have multiple seller UTxOs as input and therefore output
  --       expected tokens need to be specified as contract params, and generated script must
  --       ensure that only expected tokens get transferred; if unexpected tokens are present
  --       as input UTxOs, then script must fail at runtime
  -- TODO: generally, onchain code should try to prevent problems caused by buggy offchain code
  -- TODO: ask Manuel about minting examples

  infix 3 _#_⇒⟨_,_⟩_,_
  data _#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} {{°r : °q °.⇒⟨ °l ⟩ °q′}} →
                         TickRange → State °q → Label °l → Input →
                         State °q′ → Output → Set where

    -- IN:
    -- ∙ seller:            x
    --
    -- OUT:
    -- ∙ seller:            x - 6,080,000
    -- ∙ auction reference: 5,400,000
    -- ∙ auction:           300,000 + token
    -- ∙ fee:               380,000
    --
    -- TODO: bug: doesn't check endTime ≥ t .upper; not blocker but still helpful to diagnose
    -- TODO: JF wrote "There is no specific verification applied on deployment. However, a utxo
    --       is expected to be produced for the Auction script such that ..." -- but we specify
    --       contract behavior, so we must say what contract produces
    --       however, someone else can reference our script while producing an unexpected datum
    --       (ask Manuel if EasySM can be used to also generate minting policy scripts, guarantee
    --       uniqueness of contracts preventing deploying same instance at same time, prevent double
    --       satisfaction, etc)
    deploy : ∀ {t auctionRefKey auctionKey endTime tokenNm tokenPlc minBidAmt seller x} →
      ----------------------------------------------------------------------------------------
      t #
        start auctionRefKey auctionKey ⇒⟨
          deploy endTime tokenNm tokenPlc minBidAmt ,
            [ utxo seller noDatum [ $ada x ] ] ⟩
        auction auctionKey endTime tokenNm tokenPlc minBidAmt seller nothing ,
          ( [ utxo seller noDatum [ $ada (x - 6080000) ]
            ; utxo auctionRefKey noDatum [ $ada 5400000 ]
            ; utxo auctionKey noBidDatum
                [ $ada 300000
                ; $token tokenNm tokenPlc 1 ] ] ,
            ada 380000)

    -- IN:
    -- ∙ auction reference: 5,400,000 (ignored)
    -- ∙ auction:           300,000 + token
    -- ∙ bidder:            x
    --
    -- OUT:
    -- ∙ bidder:            x - new bid amount - 680,000
    -- ∙ auction:           new bid amount + token
    -- ∙ fee:               980,000
    --
    -- TODO: unexpected contract feature: doesn't check that bidder matches newBid .key
    -- https://github.com/IntersectMBO/plinth-template/blob/main/src/AuctionValidator.hs#L113
    firstBid : ∀ {t auctionKey endTime tokenNm tokenPlc minBidAmt origSeller newBid bidder x} →
      t .upper ≤ endTime →
      fromAda (newBid .amount) ≥ fromAda minBidAmt →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller nothing ⇒⟨
          bid newBid ,
            [ utxo auctionKey noBidDatum -- TODO: accept noDatum?
                [ $ada 300000
                ; $token tokenNm tokenPlc 1 ]
            ; utxo bidder noDatum [ $ada x ] ] ⟩
        auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just newBid) ,
          ( [ utxo bidder noDatum [ $ada (x - fromAda (newBid .amount) - 680000) ]
            ; utxo auctionKey (bidDatum newBid)
                [ $ (newBid .amount)
                ; $token tokenNm tokenPlc 1 ] ] ,
            ada 980000)

    -- IN:
    -- ∙ auction reference: 5,400,000 (ignored)
    -- ∙ auction:           old bid amount + token
    -- ∙ new bidder:        x
    --
    -- OUT:
    -- ∙ old bidder:        old bid amount
    -- ∙ new bidder:        x - new bid amount - 880,000
    -- ∙ auction:           new bid amount + token
    -- ∙ fee:               880,000
    --
    -- TODO: unexpected contract feature: doesn't check that newBidder matches newBid .key
    --       as above
    nextBid : ∀ {t auctionKey endTime tokenNm tokenPlc minBidAmt origSeller oldBid newBid newBidder x} →
      t .upper ≤ endTime →
      fromAda (newBid .amount) > fromAda (oldBid .amount) →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just oldBid) ⇒⟨
          bid newBid ,
            [ utxo auctionKey (bidDatum oldBid) -- TODO: accept mismatch with auction param?
                [ $ (oldBid .amount)
                ; $token tokenNm tokenPlc 1 ]
            ; utxo newBidder noDatum [ $ada x ] ] ⟩
        auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just newBid) ,
          ( [ utxo (oldBid .key) noDatum [ $ (oldBid .amount) ]
            ; utxo newBidder noDatum [ $ada (x - fromAda (newBid .amount) - 880000) ]
            ; utxo auctionKey (bidDatum newBid)
                [ $ (newBid .amount)
                ; $token tokenNm tokenPlc 1 ] ] ,
            ada 880000)

    -- IN:
    -- ∙ auction reference: 5,400,000 (ignored)
    -- ∙ auction:           300,000 + token
    -- ∙ seller:            x
    --
    -- OUT:
    -- ∙ seller:            x - 680,000
    -- ∙ seller:            200,000 + token
    -- ∙ fee:               480,000
    --
    -- TODO: why produce two separate UTxOs for seller? abstraction level mismatch
    --       EasySM formalizes both what is done (1) offchain, to submit transaction with token UTxO
    --       and (2) onchain, to check that UTxOs included in transaction contain token UTxO
    --       but (3) balancing UTxO is not supposed to be included in submitted transaction
    --       therefore we can't statically check balancing

    -- TODO: bug: doesn't check that seller matches origSeller -- not correct
    --       seller should be param to start state, also other things i put as params to deploy
    --       should live there;
    --       seller UTxO key CAN differ
    noBidPayOut : ∀ {t auctionKey endTime tokenNm tokenPlc minBidAmt origSeller seller x} →
      t .lower ≥ endTime →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller nothing ⇒⟨
          payOut ,
            [ utxo auctionKey noBidDatum -- TODO: accept no datum?
                [ $ada 300000
                ; $token tokenNm tokenPlc 1 ]
            ; utxo seller noDatum [ $ada x ] ] ⟩
        end ,
          ( [ utxo seller noDatum [ $ada (x - 980000) ] -- TODO: this must be input seller
            ; utxo seller noDatum -- TODO: this must be apSeller
                [ $ada 200000
                ; $token tokenNm tokenPlc 1 ] ] ,
            ada 480000)

    -- IN:
    -- ∙ auction reference: 5,400,000 (ignored)
    -- ∙ auction:           highest bid amount + token
    -- ∙ seller:            x
    --
    -- OUT:
    -- ∙ seller:            x - 980,000
    -- ∙ seller:            highest bid amount
    -- ∙ highest bidder:    200,000 + token
    -- ∙ fee:               780,000
    --
    -- TODO: does UTxO for highest bidder have minimum Ada value in order to include token?
    --       yes, required by Cardano, computed from what else is in UTxO (address, token info,
    --       datum)
    -- TODO: why produce two separate UTxOs for seller? answered above
    -- TODO: bug: doesn't check that seller matches origSeller answere above
    bidPayOut : ∀ {t auctionKey endTime tokenNm tokenPlc minBidAmt origSeller highestBid seller x} →
      t .lower ≥ endTime →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just highestBid) ⇒⟨
          payOut ,
            [ utxo auctionKey (bidDatum highestBid) -- TODO: accept mismatch with auction param?
                [ $ (highestBid .amount)
                ; $token tokenNm tokenPlc 1 ]
            ; utxo seller noDatum [ $ada x ] ] ⟩
        end ,
          ( [ utxo seller noDatum [ $ada (x - 980000) ]
            ; utxo seller noDatum [ $ (highestBid .amount) ]
            ; utxo (highestBid .key) noDatum
                [ $ada 200000
                ; $token tokenNm tokenPlc 1 ] ] ,
            ada 780000)


  -- transition relation with explicit instance argument
  _⊨_#_⇒⟨_,_⟩_,_ : ∀ {°q °l °q′} → °q °.⇒⟨ °l ⟩ °q′ →
                       TickRange → State °q → Label °l → Input →
                       State °q′ → Output → Set
  _⊨_#_⇒⟨_,_⟩_,_ °r = _#_⇒⟨_,_⟩_,_ {{°r}}


  transition : ∀ {°q °l} →
                 TickRange → State °q → Label °l → Input →
                 Maybe (Σ °.State State × Output)

  transition t
      (start auctionRefKey auctionKey)
      (deploy endTime tokenNm tokenPlc minBidAmt)
      [ utxo seller noDatum [ $ada x ] ]
    = just ((_ , auction auctionKey endTime tokenNm tokenPlc minBidAmt seller nothing) ,
        [ utxo seller noDatum [ $ada (x - 6080000) ]
        ; utxo auctionRefKey noDatum [ $ada 5400000 ]
        ; utxo auctionKey noBidDatum
            [ $ada 300000
            ; $token tokenNm tokenPlc 1 ] ] ,
        ada 380000)

  transition t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller nothing)
      (bid newBid)
      [ utxo k noBidDatum [ $ada amt ; $token nm plc 1 ]
      ; utxo bidder noDatum [ $ada x ] ]
    with t .upper ≤? endTime
      | fromAda (newBid .amount) ≥? fromAda minBidAmt
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat 300000
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | yes _ | yes _ | true | true | true | true
    = just ((_ , auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just newBid)) ,
        [ utxo bidder noDatum [ $ada (x - fromAda (newBid .amount) - 680000) ]
        ; utxo auctionKey (bidDatum newBid)
            [ $ (newBid .amount)
            ; $token tokenNm tokenPlc 1 ] ] ,
        ada 680000)
  ... | _ | _ | _ | _ | _ | _ = nothing

  transition t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just oldBid))
      (bid newBid)
      [ utxo k (bidDatum b) [ $ada amt ; $token nm plc 1 ]
      ; utxo newBidder noDatum [ $ada x ] ]
    with t .upper ≤? endTime
      | fromAda (newBid .amount) ≥? fromAda (oldBid .amount)
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat fromAda (oldBid .amount)
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | yes _ | yes _ | true | true | true | true
    = just ((_ , auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just newBid)) ,
        [ utxo (oldBid .key) noDatum [ $ (oldBid .amount) ]
        ; utxo newBidder noDatum [ $ada (x - fromAda (newBid .amount) - 880000) ]
        ; utxo auctionKey (bidDatum newBid)
            [ $ (newBid .amount)
            ; $token tokenNm tokenPlc 1 ] ] ,
        ada 880000)
  ... | _ | _ | _ | _ | _ | _ = nothing

  transition t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller nothing)
      payOut
      [ utxo k noBidDatum [ $ada amt ; $token nm plc 1 ]
      ; utxo seller noDatum [ $ada x ] ]
    with t .lower ≥? endTime
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat 300000
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | yes _ | true | true | true | true
    = just ((_ , end) ,
        [ utxo seller noDatum [ $ada (x - 680000) ]
        ; utxo seller noDatum
            [ $ada 200000
            ; $token tokenNm tokenPlc 1 ] ] ,
        ada 480000)
  ... | _ | _ | _ | _ | _ = nothing

  transition t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just highestBid))
      payOut
      [ utxo k (bidDatum b) [ $ada amt ; $token nm plc 1 ]
      ; utxo seller noDatum [ $ada x ] ]
    with t .lower ≥? endTime
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat fromAda (highestBid .amount)
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | yes _ | true | true | true | true
    = just ((_ , end) ,
        [ utxo seller noDatum [ $ada (x - 980000) ]
        ; utxo seller noDatum [ $ (highestBid .amount) ]
        ; utxo (highestBid .key) noDatum
            [ $ada 200000
            ; $token tokenNm tokenPlc 1 ] ] ,
        ada 780000)
  ... | _ | _ | _ | _ | _ = nothing

  transition _ _ _ _ = nothing


{-
  correctness : ∀ {°q °l °q′}
                  t q l x q′ y →
                  Σ (°q °.⇒⟨ °l ⟩ °q′) (_⊨ t # q ⇒⟨ l , x ⟩ q′ , y) ⇔
                    transition t q l x ≡ just ((°q′ , q′) , y)

  correctness t
      (start auctionRefKey auctionKey)
      (deploy endTime tokenNm tokenPlc minBidAmt)
      [ utxo seller noDatum [ $ada x ] ]
      _ _
    = (λ { (_ , deploy) → refl}) , λ { refl → _ , deploy }

  correctness _ (start _ _) (deploy _ _ _ _)
      [ utxo _ noDatum [] ]               _ _ = (λ ()) , λ ()

  correctness _ (start _ _) (deploy _ _ _ _)
      [ utxo _ noDatum [ $token _ _ _ ] ] _ _ = (λ ()) , λ ()

  correctness _ (start _ _) (deploy _ _ _ _)
      [ utxo _ noDatum (_ ∷ _ ∷ _) ]      _ _ = (λ ()) , λ ()

  correctness _ (start _ _) (deploy _ _ _ _)
      [ utxo _ noBidDatum _ ]             _ _ = (λ ()) , λ ()

  correctness _ (start _ _) (deploy _ _ _ _)
      [ utxo _ (bidDatum _) _ ]           _ _ = (λ ()) , λ ()

  correctness _ (start _ _) (deploy _ _ _ _) []          _ _ = (λ ()) , λ ()
  correctness _ (start _ _) (deploy _ _ _ _) (_ ∷ _ ∷ _) _ _ = (λ ()) , λ ()
  correctness _ (start _ _) (bid _)          _           _ _ = (λ ()) , λ ()
  correctness _ (start _ _) payOut           _           _ _ = (λ ()) , λ ()

  correctness t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller nothing)
      (bid newBid)
      [ utxo k noBidDatum [ $ada amt ; $token nm plc 1 ]
      ; utxo bidder noDatum [ $ada x ] ]
      _ _
    with t .upper ≤? endTime
      | fromAda (newBid .amount) ≥? fromAda minBidAmt
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat 300000
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | no ¬c₁ | _      | _     | _     | _     | _     = {!!}
  ... | yes _  | no ¬c₂ | _     | _     | _     | _     = {!!}
  ... | yes _  | yes _  | false | _     | _     | _     = {!!}
  ... | yes _  | yes _  | true  | false | _     | _     = {!!}
  ... | yes _  | yes _  | true  | true  | false | _     = {!!}
  ... | yes c₁ | yes c₂ | true  | true  | true  | false = {!!}
  ... | yes c₁ | yes c₂ | true  | true  | true  | true  = {!!}

  correctness t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just oldBid))
      (bid newBid)
      [ utxo k (bidDatum b) [ $ada amt ; $token nm plc 1 ]
      ; utxo newBidder noDatum [ $ada x ] ]
      _ _
    with t .upper ≤? endTime
      | fromAda (newBid .amount) ≥? fromAda (oldBid .amount)
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat fromAda (oldBid .amount)
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | no ¬c₁ | _      | _     | _     | _     | _     = {!!}
  ... | yes _  | no ¬c₂ | _     | _     | _     | _     = {!!}
  ... | yes _  | yes _  | false | _     | _     | _     = {!!}
  ... | yes _  | yes _  | true  | false | _     | _     = {!!}
  ... | yes _  | yes _  | true  | true  | false | _     = {!!}
  ... | yes c₁ | yes c₂ | true  | true  | true  | false = {!!}
  ... | yes c₁ | yes c₂ | true  | true  | true  | true  = {!!}

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ utxo _ (bidDatum _) []
      ; _ ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ utxo _ (bidDatum _) [ _ ]
      ; _ ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ utxo _ (bidDatum _) [ x ; y ]
      ; _ ]
      _ _ = {!!}

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ utxo _ (bidDatum _) (_ ∷ _ ∷ _ ∷ _)
      ; _ ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ utxo _ noDatum _
      ; _ ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ utxo _ noBidDatum _
      ; _ ]
      _ _ = {!!}

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ _
      ; utxo _ noDatum [] ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ _
      ; utxo _ noDatum [ $token _ _ _ ] ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ _
      ; utxo _ noDatum (_ ∷ _ ∷ _) ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ _
      ; utxo _ noBidDatum _ ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _)
      [ _
      ; utxo _ (bidDatum _) _ ]
      _ _ = (λ ()) , λ ()

  correctness _ (auction _ _ _ _ _ _ _) (bid _) []              _ _ = (λ ()) , λ ()
  correctness _ (auction _ _ _ _ _ _ _) (bid _) [ _ ]           _ _ = (λ ()) , λ ()
  correctness _ (auction _ _ _ _ _ _ _) (bid _) (_ ∷ _ ∷ _ ∷ _) _ _ = (λ ()) , λ ()

  correctness t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller nothing)
      payOut
      [ utxo k noBidDatum [ $ada amt ; $token nm plc 1 ]
      ; utxo seller noDatum [ $ada x ] ]
      _ _
    with t .lower ≥? endTime
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat 300000
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | no ¬c₁ | _     | _     | _     | _     = {!!}
  ... | yes _  | false | _     | _     | _     = {!!}
  ... | yes _  | true  | false | _     | _     = {!!}
  ... | yes _  | true  | true  | false | _     = {!!}
  ... | yes c₁ | true  | true  | true  | false = {!!}
  ... | yes c₁ | true  | true  | true  | true  = {!!}

  correctness t
      (auction auctionKey endTime tokenNm tokenPlc minBidAmt origSeller (just highestBid))
      payOut
      [ utxo k (bidDatum b) [ $ada amt ; $token nm plc 1 ]
      ; utxo seller noDatum [ $ada x ] ]
      _ _
    with t .lower ≥? endTime
      | k ≟ᴮKey auctionKey
      | amt ≟ᴮNat fromAda (highestBid .amount)
      | nm ≟ᴮStr tokenNm
      | plc ≟ᴮStr tokenPlc
  ... | no ¬c₁ | _     | _     | _     | _     = {!!}
  ... | yes _  | false | _     | _     | _     = {!!}
  ... | yes _  | true  | false | _     | _     = {!!}
  ... | yes _  | true  | true  | false | _     = {!!}
  ... | yes c₁ | true  | true  | true  | false = {!!}
  ... | yes c₁ | true  | true  | true  | true  = {!!}

  correctness _ (auction _ _ _ _ _ _ _) payOut []              _ _ = (λ ()) , λ ()
  correctness _ (auction _ _ _ _ _ _ _) payOut [ _ ]           _ _ = (λ ()) , λ ()
  correctness _ (auction _ _ _ _ _ _ _) payOut (_ ∷ _ ∷ _ ∷ _) _ _ = (λ ()) , λ ()

  correctness _ end (deploy _ _ _ _) _ _ _ = (λ ()) , λ ()
  correctness _ end (bid _)          _ _ _ = (λ ()) , λ ()
  correctness _ end payOut           _ _ _ = (λ ()) , λ ()
-}


----------------------------------------------------------------------------------------------------
