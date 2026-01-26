----------------------------------------------------------------------------------------------------

-- auction contract (SADFA version, indexed by DFA)
-- NOTE: second draft with comments based on SC group feedback


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module SADFA.Auction-V2 where

open import DFA.Auction public
open import SADFA public


----------------------------------------------------------------------------------------------------

module Auction-SADFA2 where
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
    start   : ∀ (auctionRefKey auctionKey : Key) (apSeller : Key) (tokenNm tokenPlc : String)
                (minBidAmt : Amount ada) (endTime : Tick) → State °.start
    auction : ∀ (auctionKey : Key) (apSeller : Key) (tokenNm tokenPlc : String)
                (minBidAmt : Amount ada) (endTime : Tick) (highestBid : Maybe Bid) →
                State °.auction
    end     : State °.end

  initialState : Key → Key → Key → String → String → Amount ada → Tick → State °.initialState
  initialState = start

  data Label : °.Label → Set where
    deploy : Label °.deploy
    bid    : ∀ (newBid : Bid) → Label °.bid
    payOut : Label °.payOut

  Input : Set
  Input = List (UTxO (Either Unit (Maybe Bid)))

  Output : Set
  Output = List (UTxO (Either Unit (Maybe Bid)))

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
    deploy : ∀ {t auctionRefKey auctionKey apSeller tokenNm tokenPlc minBidAmt endTime
                inputSeller x} →
      ----------------------------------------------------------------------------------------
      t #
        start auctionRefKey auctionKey apSeller tokenNm tokenPlc minBidAmt endTime ⇒⟨
          deploy ,
            [ utxo inputSeller noDatum [ $ada x ] ] ⟩
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime nothing ,
            [ utxo inputSeller noDatum [ $ada (x - 6080000) ]
            ; utxo auctionRefKey noDatum [ $ada 5400000 ]
            ; utxo auctionKey noBidDatum
                [ $ada 300000
                ; $token tokenNm tokenPlc 1 ] ]

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
    firstBid : ∀ {t auctionKey apSeller tokenNm tokenPlc minBidAmt endTime newBid bidder x} →
      t .upper ≤ endTime →
      fromAda (newBid .amount) ≥ fromAda minBidAmt →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime nothing ⇒⟨
          bid newBid ,
            [ utxo auctionKey noBidDatum -- TODO: accept noDatum?
                [ $ada 300000
                ; $token tokenNm tokenPlc 1 ]
            ; utxo bidder noDatum [ $ada x ] ] ⟩
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime (just newBid) ,
            [ utxo bidder noDatum [ $ada (x - fromAda (newBid .amount) - 680000) ]
            ; utxo auctionKey (bidDatum newBid)
                [ $ (newBid .amount)
                ; $token tokenNm tokenPlc 1 ] ]

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
    nextBid : ∀ {t auctionKey apSeller tokenNm tokenPlc minBidAmt endTime oldBid newBid
                 newBidder x} →
      t .upper ≤ endTime →
      fromAda (newBid .amount) > fromAda (oldBid .amount) →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime (just oldBid) ⇒⟨
          bid newBid ,
            [ utxo auctionKey (bidDatum oldBid)
                [ $ (oldBid .amount)
                ; $token tokenNm tokenPlc 1 ]
            ; utxo newBidder noDatum [ $ada x ] ] ⟩
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime (just newBid) ,
            [ utxo (oldBid .key) noDatum [ $ (oldBid .amount) ]
            ; utxo newBidder noDatum [ $ada (x - fromAda (newBid .amount) - 880000) ]
            ; utxo auctionKey (bidDatum newBid)
                [ $ (newBid .amount)
                ; $token tokenNm tokenPlc 1 ] ]

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
    noBidPayOut : ∀ {t auctionKey apSeller tokenNm tokenPlc minBidAmt endTime inputSeller x} →
      t .lower ≥ endTime →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime nothing ⇒⟨
          payOut ,
            [ utxo auctionKey noBidDatum -- TODO: accept no datum?
                [ $ada 300000
                ; $token tokenNm tokenPlc 1 ]
            ; utxo inputSeller noDatum [ $ada x ] ] ⟩
        end ,
            [ utxo inputSeller noDatum [ $ada (x - 980000) ]
            ; utxo apSeller noDatum
                [ $ada 200000
                ; $token tokenNm tokenPlc 1 ] ]

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
    bidPayOut : ∀ {t auctionKey apSeller tokenNm tokenPlc minBidAmt endTime highestBid
                   inputSeller x} →
      t .lower ≥ endTime →
      ----------------------------------------------------------------------------------------
      t #
        auction auctionKey apSeller tokenNm tokenPlc minBidAmt endTime (just highestBid) ⇒⟨
          payOut ,
            [ utxo auctionKey (bidDatum highestBid)
                [ $ (highestBid .amount)
                ; $token tokenNm tokenPlc 1 ]
            ; utxo inputSeller noDatum [ $ada x ] ] ⟩
        end ,
            [ utxo inputSeller noDatum [ $ada (x - 980000) ]
            ; utxo apSeller noDatum [ $ (highestBid .amount) ]
            ; utxo (highestBid .key) noDatum
                [ $ada 200000
                ; $token tokenNm tokenPlc 1 ] ]


----------------------------------------------------------------------------------------------------
