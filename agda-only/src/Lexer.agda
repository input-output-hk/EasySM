----------------------------------------------------------------------------------------------------

-- lexer for generic S-expressions, with C-like escape sequences, but Lisp-like comments


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module Lexer where

open import Machine public


----------------------------------------------------------------------------------------------------

showChar : Char → String
showChar ' '  = "\\ " -- space
showChar '\t' = "\\t" -- tab
showChar '\r' = "\\r" -- carriage return
showChar '\n' = "\\n" -- line feed
showChar '('  = "\\(" -- begin list
showChar ')'  = "\\)" -- end list
showChar ';'  = "\\;" -- comment
showChar c    = String.fromList [ c ]

module LexerThings where
  Atom : Set
  Atom = String

  showAtom : Atom → String
  showAtom str = String.concat (map showChar (String.toList str))

  data Token : Set where
    atom      : Atom → Token
    beginList : Token
    endList   : Token

  showToken : Token → String
  showToken (atom a)  = showAtom a
  showToken beginList = "("
  showToken endList   = ")"

  showMaybeTokens : List (Maybe Token) → String -- TODO: delete this
  showMaybeTokens []             = ""
  showMaybeTokens (nothing ∷ ms) = "nothing ; " ++ showMaybeTokens ms
  showMaybeTokens (just tk ∷ ms) = "(just " ++ showToken tk ++ ") ; " ++ showMaybeTokens ms

  -- de-accumulate
  atomFrom : List Char → Token
  atomFrom acc = atom (String.fromList (reverse acc))

  Lexer : Set
  Lexer = ∞Machine (Maybe Char) (List Token)

  mutual
    awaitToken : Lexer
    awaitToken .on (just ' ')  = [] , just awaitToken
    awaitToken .on (just '\t') = [] , just awaitToken
    awaitToken .on (just '\r') = [] , just awaitToken
    awaitToken .on (just '\n') = [] , just awaitToken
    awaitToken .on (just '(')  = [ beginList ] , just awaitToken
    awaitToken .on (just ')')  = [ endList ] , just awaitToken
    awaitToken .on (just ';')  = [] , just awaitComment
    awaitToken .on (just '\\') = [] , just (awaitEscape [])
    awaitToken .on (just c)    = [] , just (awaitAtom [ c ])
    awaitToken .on nothing     = [] , nothing

    awaitComment : Lexer
    awaitComment .on (just '\n') = [] , just awaitToken
    awaitComment .on (just c)    = [] , just awaitComment
    awaitComment .on nothing     = [] , nothing

    awaitEscape : List Char → Lexer
    awaitEscape acc .on (just ' ')  = [] , just (awaitAtom (' '  ∷ acc))
    awaitEscape acc .on (just 't')  = [] , just (awaitAtom ('\t' ∷ acc))
    awaitEscape acc .on (just 'r')  = [] , just (awaitAtom ('\r' ∷ acc))
    awaitEscape acc .on (just 'n')  = [] , just (awaitAtom ('\n' ∷ acc))
    awaitEscape acc .on (just '(')  = [] , just (awaitAtom ('('  ∷ acc))
    awaitEscape acc .on (just ')')  = [] , just (awaitAtom (')'  ∷ acc))
    awaitEscape acc .on (just ';')  = [] , just (awaitAtom (';'  ∷ acc))
    awaitEscape acc .on (just '\\') = [] , just (awaitAtom ('\\' ∷ acc))
    awaitEscape acc .on (just c)    = [] , just (awaitAtom (c ∷ '\\' ∷ acc))
    awaitEscape acc .on nothing     = [ atomFrom ('\\' ∷ acc) ] , nothing

    awaitAtom : List Char → Lexer
    awaitAtom acc .on (just ' ')  = [ atomFrom acc ] , just awaitToken
    awaitAtom acc .on (just '\t') = [ atomFrom acc ] , just awaitToken
    awaitAtom acc .on (just '\r') = [ atomFrom acc ] , just awaitToken
    awaitAtom acc .on (just '\n') = [ atomFrom acc ] , just awaitToken
    awaitAtom acc .on (just '(')  = (atomFrom acc ∷ [ beginList ]) , just awaitToken
    awaitAtom acc .on (just ')')  = (atomFrom acc ∷ [ endList ]) , just awaitToken
    awaitAtom acc .on (just ';')  = [ atomFrom acc ] , just awaitComment
    awaitAtom acc .on (just '\\') = [] , just (awaitEscape acc)
    awaitAtom acc .on (just c)    = [] , just (awaitAtom (c ∷ acc))
    awaitAtom acc .on nothing     = [ atomFrom acc ] , nothing

  lex : String → List Token
  lex str = List′.concat (∞MachineThings.PutMaybe.run awaitToken (String.toList str))

open LexerThings public using (Atom ; showAtom ; Token ; atom ; beginList ; endList ; showToken ;
    lex)


----------------------------------------------------------------------------------------------------
