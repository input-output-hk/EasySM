----------------------------------------------------------------------------------------------------

-- Mealy/Moore-like machines, or Shannon’s discrete transducers, or stream processors

-- G.H. Mealy (1955) “A method for synthesizing sequential circuits”
-- E.F. Moore (1952) “A simplified universal Turing machine”
-- C.E. Shannon (1948) “A mathematical theory of communication”


----------------------------------------------------------------------------------------------------

{-# OPTIONS --guardedness --sized-types #-}

module Machine where

open import Prelude public


----------------------------------------------------------------------------------------------------

module ∞MachineThings where
  -- machine that consumes input and produces output, and either stops or continues
  mutual
    record ∞Machine {𝓍 𝓎} (X : Set 𝓍) (Y : Set 𝓎) : Set (𝓍 ⊔ 𝓎) where
      coinductive
      field
        on : X → Machine X Y

    Machine : ∀ {𝓍 𝓎} → Set 𝓍 → Set 𝓎 → Set (𝓍 ⊔ 𝓎)
    Machine X Y = Y × Maybe (∞Machine X Y)

  open ∞Machine public

  -- strong bisimilarity of machines
  module _ where
    mutual
      infix 3 _∞≍_
      record _∞≍_ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} (m₁ m₂ : ∞Machine X Y) : Set (𝓍 ⊔ 𝓎) where
        coinductive
        field
          on² : ∀ x → m₁ .on x ≍ m₂ .on x

      infix 3 _≍_
      data _≍_ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} : Machine X Y → Machine X Y → Set (𝓍 ⊔ 𝓎) where
        stop² : ∀ {y₁ y₂ : Y} {{yeq : y₁ ≡ y₂}} → y₁ , nothing ≍ y₂ , nothing
        go²   : ∀ {y₁ y₂ : Y} {m₁ m₂} {{yeq : y₁ ≡ y₂}} → m₁ ∞≍ m₂ → y₁ , just m₁ ≍ y₂ , just m₂

    open _∞≍_ public

    mutual
      refl∞≍ : ∀ {𝓍} {X : Set 𝓍} {m : ∞Machine X X} → m ∞≍ m
      refl∞≍ .on² x = refl≍

      refl≍ : ∀ {𝓍} {X : Set 𝓍} {p : Machine X X} → p ≍ p
      refl≍ {p = _ , nothing} = stop²
      refl≍ {p = _ , just _}  = go² refl∞≍

    mutual
      sym∞≍ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {m₁ m₂ : ∞Machine X Y} → m₁ ∞≍ m₂ → m₂ ∞≍ m₁
      sym∞≍ meq .on² x = sym≍ (meq .on² x)

      sym≍ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {p₁ p₂ : Machine X Y} → p₁ ≍ p₂ → p₂ ≍ p₁
      sym≍ (stop² {{yeq}})   = stop² {{sym yeq}}
      sym≍ (go² {{yeq}} meq) = go² {{sym yeq}} (sym∞≍ meq)

    mutual
      trans∞≍ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {m₁ m₂ m₃ : ∞Machine X Y} →
                  m₁ ∞≍ m₂ → m₂ ∞≍ m₃ → m₁ ∞≍ m₃
      trans∞≍ meq₁ meq₂ .on² x = trans≍ (meq₁ .on² x) (meq₂ .on² x)

      trans≍ : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} {p₁ p₂ p₃ : Machine X Y} →
                  p₁ ≍ p₂ → p₂ ≍ p₃ → p₁ ≍ p₃
      trans≍ (stop² {{yeq₁}})    (stop² {{yeq₂}})    = stop² {{trans yeq₁ yeq₂}}
      trans≍ (go² {{yeq₁}} meq₁) (go² {{yeq₂}} meq₂) = go² {{trans yeq₁ yeq₂}} (trans∞≍ meq₁ meq₂)

  -- category of machines
  module _ where
    fromFun : ∀ {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} → (X → Y) → ∞Machine X Y
    fromFun f .on x = f x , just (fromFun f)

    id : ∀ {𝓍} {X : Set 𝓍} → ∞Machine X X
    id = fromFun Function′.id

    infixr 9 _∘_
    _∘_ : ∀ {𝓍 𝓎 𝓏} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} →
            ∞Machine Y Z → ∞Machine X Y → ∞Machine X Z
    (m₂ ∘ m₁) .on x with m₁ .on x
    (m₂ ∘ m₁) .on x | y , nothing  with m₂ .on y
    (m₂ ∘ m₁) .on x | y , nothing  | z , nothing  = z , nothing
    (m₂ ∘ m₁) .on x | y , nothing  | z , just _   = z , nothing
    (m₂ ∘ m₁) .on x | y , just m₁′ with m₂ .on y
    (m₂ ∘ m₁) .on x | y , just m₁′ | z , nothing  = z , nothing
    (m₂ ∘ m₁) .on x | y , just m₁′ | z , just m₂′ = z , just (m₂′ ∘ m₁′)

    lid∘ : ∀ {𝓍} {X : Set 𝓍} (m : ∞Machine X X) → id ∘ m ∞≍ m
    lid∘ m .on² x     with m .on x
    ... | y , nothing   = stop²
    ... | y , just m′   = go² (lid∘ m′)

    rid∘ : ∀ {𝓍} {X : Set 𝓍} (m : ∞Machine X X) → m ∘ id ∞≍ m
    rid∘ m .on² x     with m .on x
    ... | y , nothing   = stop²
    ... | y , just m′   = go² (rid∘ m′)

    ass∘ : ∀ {𝓍 𝓎 𝓏 𝒶} {X : Set 𝓍} {Y : Set 𝓎} {Z : Set 𝓏} {A : Set 𝒶}
             (m₃ : ∞Machine Z A) (m₂ : ∞Machine Y Z) (m₁ : ∞Machine X Y) →
             m₃ ∘ (m₂ ∘ m₁) ∞≍ (m₃ ∘ m₂) ∘ m₁
    ass∘ m₃ m₂ m₁ .on² x with m₁ .on x
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  with m₂ .on y
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  | z , nothing  with m₃ .on z
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  | z , nothing  | _ , nothing  = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  | z , nothing  | _ , just _   = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  | z , just m₂′ with m₃ .on z
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  | z , just m₂′ | _ , nothing  = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , nothing  | z , just m₂′ | _ , just _   = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ with m₂ .on y
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ | z , nothing  with m₃ .on z
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ | z , nothing  | _ , nothing  = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ | z , nothing  | _ , just _   = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ | z , just m₂′ with m₃ .on z
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ | z , just m₂′ | _ , nothing  = stop²
    ass∘ m₃ m₂ m₁ .on² x | y , just m₁′ | z , just m₂′ | _ , just m₃′ = go² (ass∘ m₃′ m₂′ m₁′)

  -- any machine
  module Any {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} where
    -- potentially infinite run
    -- returns only output
    corun : ∞Machine X Y → Colist X → Colist Y
    corun m []        = []
    corun m (x ∷ xs)  with m .on x
    ... | y , nothing   = y ∷ ♯ []
    ... | y , just m′   = y ∷ ♯ corun m′ (♭ xs)

    -- finite run until stop or end of input
    -- returns output, unconsumed input, and final machine
    run* : ∞Machine X Y → List X →
           List Y × List X × Maybe (∞Machine X Y)
    run* m xs = aux [] m xs
      where
        aux : List Y → ∞Machine X Y → List X →
              List Y × List X × Maybe (∞Machine X Y)
        aux acc m []       = reverse acc , [] , just m
        aux acc m (x ∷ xs) with m .on x
        ... | y , nothing    = reverse (y ∷ acc) , xs , nothing
        ... | y , just m′    = aux (y ∷ acc) m′ xs

    -- finite run until stop or end of input
    -- returns only output
    run : ∞Machine X Y → List X → List Y
    run m xs = fst (run* m xs)

    step : ∞Machine X Y → X → Y
    step m x = fst (m .on x)

  -- machine that may fail to produce output
  module GetMaybe {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} where
    -- finite run until failure, stop, or end of input
    -- returns output produced before failure, unconsumed input, and final machine
    run* : ∞Machine X (Maybe Y) → List X →
           List Y × List X × Maybe (∞Machine X (Maybe Y))
    run* m xs = aux [] m xs
      where
        aux : List Y → ∞Machine X (Maybe Y) → List X →
              List Y × List X × Maybe (∞Machine X (Maybe Y))
        aux acc m []            = reverse acc , [] , just m
        aux acc m (x ∷ xs)      with m .on x
        ... | nothing , m′        = reverse acc , xs , m′
        ... | just y  , nothing   = reverse (y ∷ acc) , xs , nothing
        ... | just y  , just m′   = aux (y ∷ acc) m′ xs

    -- finite run until failure, stop, or end of input
    -- returns only output produced before failure
    run : ∞Machine X (Maybe Y) → List X → List Y
    run m xs = fst (run* m xs)

    step : ∞Machine X (Maybe Y) → X → Maybe Y
    step m x = fst (m .on x)

  -- machine that either produces output or fails
  module GetEither {𝓍 𝓎 ℯ} {X : Set 𝓍} {Y : Set 𝓎} {E : Set ℯ} where
    -- finite run until failure, stop, or end of input
    -- returns output produced before failure, failure cause, unconsumed input, and final machine
    run* : ∞Machine X (Either E Y) → List X →
           (List Y × Maybe E) × List X × Maybe (∞Machine X (Either E Y))
    run* m xs = aux [] m xs
      where
        aux : List Y → ∞Machine X (Either E Y) → List X →
              (List Y × Maybe E) × List X × Maybe (∞Machine X (Either E Y))
        aux acc m []           = (reverse acc , nothing) , [] , nothing
        aux acc m (x ∷ xs)     with m .on x
        ... | fail e , m′        = (reverse acc , just e) , xs , m′
        ... | ok y   , nothing   = (reverse (y ∷ acc) , nothing) , xs , nothing
        ... | ok y   , just m′   = aux (y ∷ acc) m′ xs

    -- finite run until failure, stop, or end of input
    -- returns only output produced before failure and failure cause
    run : ∞Machine X (Either E Y) → List X → List Y × Maybe E
    run m xs = fst (run* m xs)

    step : ∞Machine X (Either E Y) → X → Either E Y
    step m x = fst (m .on x)

  -- machine that consumes end of input explicitly
  module PutMaybe {𝓍 𝓎} {X : Set 𝓍} {Y : Set 𝓎} where
    -- finite run until stop or end of input
    -- returns output, unconsumed input, and final machine
    run* : ∞Machine (Maybe X) Y → List X →
           List Y × List X × Maybe (∞Machine (Maybe X) Y)
    run* m xs = aux [] m xs
      where
        aux : List Y → ∞Machine (Maybe X) Y → List X →
              List Y × List X × Maybe (∞Machine (Maybe X) Y)
        aux acc m []       with m .on nothing
        ... | y , m′         = reverse (y ∷ acc) , [] , m′
        aux acc m (x ∷ xs) with m .on (just x)
        ... | y , nothing    = reverse (y ∷ acc) , xs , nothing
        ... | y , just m′    = aux (y ∷ acc) m′ xs

    -- finite run until stop or end of input
    -- returns only output
    run : ∞Machine (Maybe X) Y → List X → List Y
    run m xs = fst (run* m xs)

    step : ∞Machine (Maybe X) Y → Maybe X → Y
    step m x = fst (m .on x)

  open Any public

open ∞MachineThings public using (∞Machine ; on ; Machine ; corun ; run* ; run)


----------------------------------------------------------------------------------------------------
