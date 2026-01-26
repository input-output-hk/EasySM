----------------------------------------------------------------------------------------------------

-- parser for generic S-expressions


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module Parser where

open import Lexer public


----------------------------------------------------------------------------------------------------

module TermParserThings where
  data Term : Set where
    atom : Atom → Term
    list : List Term → Term

  mutual
    showTerm : Term → String
    showTerm (atom a)   = showAtom a
    showTerm (list tms) = showTerms tms

    showTerms : List Term → String
    showTerms []         = "()"
    showTerms (tm ∷ tms) = "(" ++ showTerm tm ++ aux tms
      where
        aux : List Term → String
        aux []         = ")"
        aux (tm ∷ tms) = " " ++ showTerm tm ++ aux tms
    -- NOTE: termination checker failure
    -- showTerms tms = "(" ++ String.intersperse " " (map showTerm tms) ++ ")"

  -- TODO: delete this
  showMaybeTerms : List (Maybe Term) → String
  showMaybeTerms []             = ""
  showMaybeTerms (nothing ∷ ms) = "nothing ; " ++ showMaybeTerms ms
  showMaybeTerms (just tm ∷ ms) = "(just " ++ showTerm tm ++ ") ; " ++ showMaybeTerms ms

  data TermParserErr : Set where
    impossible      : String → TermParserErr -- TODO: clean this up
    endOfList       : TermParserErr
    endOfLine       : TermParserErr
    endOfLineInList : TermParserErr

  showTermParserErr : TermParserErr → String
  showTermParserErr (impossible str) = "impossible! " ++ str -- TODO: clean this up
  showTermParserErr endOfList        = "unexpected end of list while awaiting term"
  showTermParserErr endOfLine        = "unexpected end of line while awaiting term"
  showTermParserErr endOfLineInList  = "unexpected end of line while awaiting term or end of list"

  -- de-accumulate
  listFrom : List Term → Term
  listFrom acc = list (reverse acc)

  TermParser : Set
  TermParser = ∞Machine (Maybe Token) (Either TermParserErr (Maybe Term))

  mutual
    awaitTerm : TermParser
    awaitTerm .on (just beginList) = ok nothing , just (awaitList [ [] ])
    awaitTerm .on (just endList)   = fail endOfList , nothing
    awaitTerm .on (just (atom a))  = ok (just (atom a)) , just awaitTerm
    awaitTerm .on nothing          = ok nothing , nothing

    awaitList : List⁺ (List Term) → TermParser
    awaitList accs                .on (just beginList) = ok nothing , just (awaitList
                                                           ([] ∷ List⁺′.toList accs))
    awaitList (acc ∷ [])          .on (just endList)   = ok (just (listFrom acc)) , just awaitTerm
    awaitList (acc ∷ acc′ ∷ accs) .on (just endList)   = ok nothing , just (awaitList
                                                           ((listFrom acc ∷ acc′) ∷ accs))
    awaitList (acc ∷ accs)        .on (just (atom a))  = ok nothing , just (awaitList
                                                           ((atom a ∷ acc) ∷ accs))
    awaitList _                   .on nothing          = fail endOfLineInList , nothing

  parseTerm : List Token → Either TermParserErr (List Term)
  parseTerm tks with ∞MachineThings.GetEither.run* awaitTerm (map just tks List′.++ [ nothing ])
  parseTerm tks | (_   , just err) , _    , _ = fail err
  parseTerm tks | (tms , nothing)  , []   , _ with catMaybes tms
  parseTerm tks | (tms , nothing)  , []   , _ | []   = fail endOfLine
  parseTerm tks | (tms , nothing)  , []   , _ | tms′ = ok tms′
  -- TODO: make this actually impossible
  parseTerm tks | (tms , nothing)  , tks′ , _ = fail (impossible ("\ntms = " ++
                                                  showMaybeTerms tms ++ "\ntks′ = " ++
                                                  LexerThings.showMaybeTokens tks′))

open TermParserThings public using (Term ; atom ; list ; showTerm ; showTerms ; TermParserErr ;
    showTermParserErr ; parseTerm)


----------------------------------------------------------------------------------------------------

-- extra parsers

data NatParserErr : Set where
  notAtom    : Term → NatParserErr
  notDigit   : Char → NatParserErr

showNatParserErr : NatParserErr → String
showNatParserErr (notAtom tm) = "invalid natural '" ++ showTerm tm ++ "'"
showNatParserErr (notDigit c) = "invalid digit '" ++ showChar c ++ "'"

NatParser : Set
NatParser = ∞Machine Term (Either NatParserErr Nat)

awaitNat : NatParser
awaitNat .on (atom a) = aux 0 (String.toList a) , just awaitNat
  where
    -- NOTE: we could use Data.Nat.Show.readMaybe, but then we would not know failure cause
    aux : Nat → List Char → Either NatParserErr Nat
    aux n []       = ok n
    aux n (c ∷ cs) with isDigit c
    ... | false      = fail (notDigit c)
    ... | true       = aux (10 * n + natFrom c - natFrom '0') cs
awaitNat .on tm       = fail (notAtom tm) , just awaitNat

parseNat : Term → Either NatParserErr Nat
parseNat tm = ∞MachineThings.GetEither.step awaitNat tm


----------------------------------------------------------------------------------------------------
