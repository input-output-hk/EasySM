----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module tmp.Colist where

open import Prelude public


----------------------------------------------------------------------------------------------------

-- investigation of colist variants

module TrailedColistThings where
  data TrailedColist {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
    []&_ : Y → TrailedColist X Y
    _∷_  : X → ∞ (TrailedColist X Y) → TrailedColist X Y

  sequence : ∀ {ℓ} {X Y : Set ℓ} → TrailedColist (IO X) Y → IO (TrailedColist X Y)
  sequence ([]& y)    = returnIO ([]& y)
  sequence (op ∷ ops) = bindIO (♯ op) λ x → ♯
                          bindIO (♯ sequence (♭ ops)) λ xs → ♯
                            returnIO (x ∷ ♯ xs)
  -- NOTE: termination checker failure
  -- sequence (op ∷ ops) = do x  ← op
  --                          xs ← sequence (♭ ops)
  --                          returnIO (x ∷ ♯ xs)

module UnsafeSizedColistThings where
  open import Codata.Sized.Colist public using ([] ; _∷_) renaming (Colist to SizedColist)
  open import Codata.Sized.Thunk public using (force)

  sequence : ∀ {𝓍} {X : Set 𝓍} → SizedColist (IO X) Sizeω → IO (SizedColist X Sizeω)
  sequence []         = returnIO []
  sequence (op ∷ ops) = bindIO (♯ op) λ x → ♯
                          bindIO (♯ sequence (ops .force)) λ xs → ♯
                            returnIO (x ∷ λ where .force → xs)
  -- NOTE: termination checker failure
  -- sequence (op ∷ ops) = do x  ← op
  --                          xs ← sequence (ops .force)
  --                          returnIO (x ∷ λ where .force → xs)

module SafeSizedColistThings where
  mutual
    infixr 5 _∷_
    data SizedColist {𝓍} (X : Set 𝓍) (i : Size) : Set 𝓍 where
      []  : SizedColist X i
      _∷_ : X → ∞SizedColist X i → SizedColist X i

    record ∞SizedColist {𝓍} (X : Set 𝓍) (i : Size) : Set 𝓍 where
      coinductive
      field
        force : ∀ {j : Size< i} → SizedColist X j

  open ∞SizedColist public

  sequence : ∀ {𝓍} {X : Set 𝓍} → SizedColist (IO X) Sizeω → IO (SizedColist X Sizeω)
  sequence []         = returnIO []
  sequence (op ∷ ops) = bindIO (♯ op) λ x → ♯
                          bindIO (♯ sequence (ops .force)) λ xs → ♯
                            returnIO (x ∷ λ where .force → xs)
  -- NOTE: termination checker failure
  -- sequence (op ∷ ops) = do x  ← op
  --                          xs ← sequence (ops .force)
  --                          returnIO (x ∷ λ where .force → xs)


----------------------------------------------------------------------------------------------------
