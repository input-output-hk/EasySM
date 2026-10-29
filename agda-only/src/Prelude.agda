----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module Prelude where

module Function′ where
  open import Function public

module List′ where
  open import Data.List public

module List⁺′ where
  open import Data.List.NonEmpty public

module Maybe′ where
  open import Data.Maybe public
  open import Data.Maybe.Properties public

module Prim where
  open import Agda.Builtin.IO public
  open import IO.Primitive.Finite public

module Reflection where
  open import Agda.Builtin.Reflection public

module Std where
  open import Data.Nat.Literals public
  open import Data.String.Literals public

module StdIO where
  open import IO public

module StdReflection where
  open import Reflection public

module String where
 open import Data.String public

module Vec′ where
  open import Data.Vec public

open import Agda.Builtin.Bool public using (Bool ; false ; true)
open import Agda.Builtin.Char public using (Char) renaming (primCharToNat to natFrom ;
    primIsDigit to isDigit ; primNatToChar to charFrom)
open import Agda.Builtin.Coinduction public using (∞ ; ♯_ ; ♭)
open import Agda.Builtin.Equality public using (_≡_ ; refl)
open import Agda.Builtin.FromNat public using (fromNat) renaming (Number to IsNat)
open import Agda.Builtin.FromString public using (IsString ; fromString)
open import Agda.Builtin.List public using (List ; [] ; _∷_)
open import Agda.Builtin.Maybe public using (Maybe ; just ; nothing)
open import Agda.Builtin.Nat public using (Nat ; zero ; suc ; _+_ ; _-_ ; _*_)
    renaming (_==_ to _≟ᴮNat_)
open import Agda.Builtin.Sigma public using (Σ ; _,_ ; fst ; snd)
open import Agda.Builtin.Size public using (Size ; Size<_) renaming (∞ to Sizeω)
open import Agda.Builtin.String public using (String) renaming (primStringAppend to infixr 5 _++_ ;
    primStringEquality to _≟ᴮStr_)
open import Agda.Builtin.Unit public using () renaming (⊤ to Unit ; tt to unit)
open import Agda.Primitive public using (Level ; _⊔_ ; Setω ; lzero ; lsuc)

open import Codata.Musical.Colist public using (Colist ; [] ; _∷_)
open import Codata.Musical.Costring public using (Costring)
open import Data.Bool public using (if_then_else_)
open import Data.Empty public using () renaming (⊥ to Empty ; ⊥-elim to abort)
open import Data.Fin public using (Fin ; zero ; suc)
open import Data.List public using (catMaybes ; length ; map ; reverse)
open import Data.List.NonEmpty public using (List⁺ ; _∷_)
open import Data.Nat public using (_≤_ ; _<_ ; _≥_ ; _>_ ; _≤?_ ; _<?_ ; _≥?_ ; _>?_)
open import Data.Nat.Show public using () renaming (show to showNat)
open import Data.Product public using (_×_)
open import Data.Sum public using () renaming (_⊎_ to Either ; inj₁ to left ; inj₂ to right)
open import Data.Unit.Polymorphic public using () renaming (⊤ to Polyunit ; tt to polyunit)
open import Data.Vec public using (Vec ; [] ; _∷_)
open import Function public using (case_of_)
open import IO public using (IO ; Main) renaming (bind to bindIO ; pure to returnIO)
open StdIO.Colist public using () renaming (mapM′ to comapM′)
open StdIO.List public using (mapM)
open import Relation.Nullary public using (Dec ; yes ; no)
open import Relation.Nullary.Negation public using (¬_) renaming (contradiction to _↯_)
open import Relation.Binary.PropositionalEquality public using (sym ; trans ; cong)


----------------------------------------------------------------------------------------------------

-- tiny extras

‼ : ∀ {𝓍} {X : Set 𝓍} {{x : X}} → X
‼ {{x}} = x

infix 1 _⇔_
_⇔_ : ∀ {𝓍 𝓎} → Set 𝓍 → Set 𝓎 → Set _
X ⇔ Y = (X → Y) × (Y → X)

lookup : ∀ {𝓍} {X : Set 𝓍} → List X → Nat → Maybe X
lookup []       _       = nothing
lookup (x ∷ _)  zero    = just x
lookup (_ ∷ xs) (suc n) = lookup xs n

instance
  natIsNat : IsNat Nat
  natIsNat = Std.number

instance
  stringIsString : IsString String
  stringIsString = Std.isString

showNats : List Nat → String
showNats ns = "(" ++ String.intersperse " " (map showNat ns) ++ ")"

-- NOTE: ';' used in these list pattern synonyms is U+037E GREEK QUESTION MARK
pattern [_] a         = a ∷ []
pattern [_;_] a b     = a ∷ b ∷ []
pattern [_;_;_] a b c = a ∷ b ∷ c ∷ []

beep : String
beep = String.fromList [ charFrom 7 ]

pattern fail x = left x
pattern ok y   = right y


----------------------------------------------------------------------------------------------------

-- colist extras

module _ where
  splitAt : ∀ {𝓍} {X : Set 𝓍} → Nat → Colist X → List X × Colist X
  splitAt zero    xs       = [] , xs
  splitAt (suc n) []       = [] , []
  splitAt (suc n) (x ∷ xs) with splitAt n (♭ xs)
  ... | xs′ , xs″            = x ∷ xs′ , xs″

  fromCostring : Costring → Colist Char
  fromCostring []       = []
  fromCostring (x ∷ xs) = x ∷ ♯ (♭ xs)


----------------------------------------------------------------------------------------------------

-- function extras

module _ where
  open Function′

  record Iso {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
    constructor mkIso
    field
      to   : X → Y
      from : Y → X
      fwd  : ∀ x → (from ∘ to) x ≡ x
      bwd  : ∀ y → (to ∘ from) y ≡ y

  open Iso

  reflIso : ∀ {𝓍} {X : Set 𝓍} → Iso X X
  reflIso = mkIso id id (λ _ → refl) λ _ → refl

  symIso : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → Iso X Y → Iso Y X
  symIso i = mkIso (i .from) (i .to) (i .bwd) (i .fwd)

  transIso : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} → Iso X Y → Iso Y Z → Iso X Z
  transIso i j = mkIso (j .to ∘ i .to) (i .from ∘ j .from)
                   (λ x → trans (cong (i .from) ((j .fwd ∘ i .to) x)) (i .fwd x))
                   λ y → trans (cong (j .to) ((i .bwd ∘ j .from) y)) (j .bwd y)

  _≐_ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} → (∀ x → Y x) → (∀ x → Y x) → Set (𝓍 ⊔ 𝓎)
  f ≐ g = ∀ x → f x ≡ g x

  congapp : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} → {f g : ∀ x → Y x} → f ≡ g → f ≐ g
  congapp refl _ = refl

  Funext : Setω
  Funext = ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : X → Set 𝓎} → {f g : ∀ x → Y x} → f ≐ g → f ≡ g


----------------------------------------------------------------------------------------------------

-- maybe extras

module _ where
  unmap-nothing : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f : X → Y} {mx} →
                    Maybe′.map f mx ≡ nothing → mx ≡ nothing
  unmap-nothing {mx = nothing} refl = refl

  unmap-just : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {f : X → Y} {mx y} →
                 Maybe′.map f mx ≡ just y → Σ X λ x → mx ≡ just x × f x ≡ y
  unmap-just {mx = just x} refl = x , refl , refl


----------------------------------------------------------------------------------------------------

-- reflection extras
-- TODO: work in progress

module MetaThings where
  open Reflection public renaming (catchTC to infix 0 try_catch_ ; quoteTC to quoteValue ;
      returnTC to return ; primQNameEquality to _≟ᴮName_ ; primQNameLess to _<?ᴮName_ ;
      primShowQName to showQualifiedName)
  open StdReflection public using (_>>=_ ; _>>_)

  pattern argv tm = arg (arg-info visible (modality relevant quantity-ω)) tm
  pattern argh tm = arg (arg-info hidden (modality relevant quantity-ω)) tm
  pattern argi tm = arg (arg-info instance′ (modality relevant quantity-ω)) tm

  instance
    errorPartIsString : IsString ErrorPart
    errorPartIsString = record
        { Constraint = λ _ → Unit
        ; fromString = λ str → strErr str
        }

  instance
    errorPartsIsString : IsString (List ErrorPart)
    errorPartsIsString = record
        { Constraint = λ _ → Unit
        ; fromString = λ str → [ strErr str ]
        }

  sequence : ∀ {𝓍} {X : Set 𝓍} → List (TC X) → TC (List X)
  sequence []         = return []
  sequence (op ∷ ops) = do x  ← op
                           xs ← sequence ops
                           return (x ∷ xs)

  showName : Name → TC String
  showName nm =
      try
        (getDefinition nm >>= λ where
          (data-cons _ _) → formatErrorParts [ termErr (con nm []) ]
          _               → formatErrorParts [ termErr (def nm []) ])
      catch
        return (showQualifiedName nm)

  getFunClauses : Name → TC (List Clause)
  getFunClauses nm =
      getDefinition nm >>= λ where
        (function cs) → return cs
        _             → typeError "not a function"

  getCtorNames : Name → TC (List Name)
  getCtorNames nm =
      getDefinition nm >>= λ where
        (data-type _ nms) → return nms
        _                 → typeError "not a data type"

  unifyValue : ∀ {𝓍} {X : Set 𝓍} → Term → X → TC Unit
  unifyValue hole x = quoteValue x >>= unify hole

  macrofy : ∀ {𝓍} {X : Set 𝓍} → (Name → TC X) → Name → Term → TC Unit
  macrofy f nm hole = f nm >>= unifyValue hole

  macro
    getType! : Name → Term → TC Unit
    getType! = macrofy getType

    getDefinition! : Name → Term → TC Unit
    getDefinition! = macrofy getDefinition

    getFunClauses! : Name → Term → TC Unit
    getFunClauses! = macrofy getFunClauses

    getCtorNames! : Name → Term → TC Unit
    getCtorNames! = macrofy getCtorNames

  -- derive show function from simple data type
  -- TODO: support complex data types
  -- TODO: finish this later
  deriveShowFun : Name → Name → TC Unit
  deriveShowFun fnNm tpNm = do
      crNms ← getCtorNames tpNm
      crCls ← sequence (map mkCtorClause crNms)
      let fnTp = pi (argv (def tpNm [])) (abs "x" (quoteTerm String))
      declareDef (argv fnNm) fnTp
      defineFun fnNm crCls
    where
      mkCtorClause : Name → TC Clause
      mkCtorClause crNm = do
          crStr ← showName crNm
          return (clause []
                   [ argv (con crNm []) ]
                   (def (quote IsString.fromString)
                     ( argh unknown
                     ∷ argh unknown
                     ∷ argv (def (quote Std.isString) [])
                     ∷ argv (lit (string crStr))
                     ∷ argi (con (quote unit) []) ∷ [])))


----------------------------------------------------------------------------------------------------

-- I/O extras

module _ where
  open StdIO using (_>>=_)

  {-# FOREIGN GHC import qualified System.IO #-}

  postulate Int : Set
  {-# COMPILE GHC Int = type Int #-}

  postulate Handle : Set
  {-# COMPILE GHC Handle = type System.IO.Handle #-}

  postulate stdout : Handle
  {-# COMPILE GHC stdout = System.IO.stdout #-}

  postulate stderr : Handle
  {-# COMPILE GHC stderr = System.IO.stderr #-}

  data BufferMode : Set where
    noBuffering    : BufferMode
    lineBuffering  : BufferMode
    blockBuffering : Maybe Int → BufferMode
  {-# COMPILE GHC BufferMode = data System.IO.BufferMode
      (System.IO.NoBuffering | System.IO.LineBuffering | System.IO.BlockBuffering) #-}

  postulate primSetBuffering : Handle → BufferMode → Prim.IO Unit
  {-# COMPILE GHC primSetBuffering = System.IO.hSetBuffering #-}

  setBuffering : Handle → BufferMode → IO Unit
  setBuffering h m = IO.lift (primSetBuffering h m)

  postulate primFlush : Handle → Prim.IO Unit
  {-# COMPILE GHC primFlush = System.IO.hFlush #-}

  flush : Handle → IO Unit
  flush h = IO.lift (primFlush h)

  putStr : String → IO Unit
  putStr s = IO.lift (Prim.putStr s)

  putStrLn : String → IO Unit
  putStrLn s = IO.lift (Prim.putStrLn s)

  getChars : IO (Colist Char)
  getChars = do s ← StdIO.getContents
                returnIO (fromCostring s)


----------------------------------------------------------------------------------------------------
