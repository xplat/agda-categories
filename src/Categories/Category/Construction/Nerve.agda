{-# OPTIONS --without-K --safe #-}


open import Level

-- Nerves of categories

module Categories.Category.Construction.Nerve (o ℓ e : Level) where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Fin using (Fin; toℕ)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor using (Functor; module Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ˡ_; _∘ʳ_)

open import Categories.Category.Construction.Functors using (Precompose)
open import Categories.Category.Construction.KanComplex (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) using (inner; IsWeakKanComplex)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Simplex using (Δ; ⟦_⟧; Δ-monotone; Δ-pointwise)
open import Categories.Category.Instance.SimplicialSet using (SimplicialSet)
open import Categories.Category.Instance.SimplicialSet.Properties (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) using (ΔSet; Δ[_]; Λ[_,_]; Λ-inj)
open import Categories.Category.Lift using (liftC; liftF; unliftF)

import Categories.Yoneda as Yoneda

open Category (SimplicialSet (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e))

-- A nerve is similar to a weak Kan Complex, but where inner horn fillers are unique.
--
-- The indexing here is tricky, but it lets us avoid extra proof conditions that the horn is an inner horn.
-- The basic idea is that if we want an n-dimensional inner horn, then we only want to allow the faces {1,2,3...n-1}
-- to be missing. We could do this by requiring proofs that the missing face is greater than 0 and less than n, but
-- this makes working with the definition _extremely_ difficult.
--
-- To avoid this, we only allow an missing face index that ranges from 0 to n-2, and then embed that index
-- into the full range of face indexes via 'inner'. This does require us to shift our indexes around a bit.
-- To make this indexing more obvious, we use the suggestively named variable 'n-1'.
record IsNerve (X : ΔSet) : Set (o ⊔ ℓ ⊔ e) where
  field
    isWeakKanComplex : IsWeakKanComplex X
  open IsWeakKanComplex isWeakKanComplex public
  field
    filler-unique : ∀ {n-1} {k : Fin n-1} (f : Λ[ ℕ.suc n-1 , inner k ] ⇒ X) (g : Δ[ ℕ.suc n-1 ] ⇒ X) → g ∘ Λ-inj (inner k) ≈ f → g ≈ filler f

Nerve⇒WeakKanComplex : ∀ {X} → IsNerve X → IsWeakKanComplex X
Nerve⇒WeakKanComplex nerve = IsNerve.isWeakKanComplex nerve

CategorialSimplex : ℕ → Category _ _ _
CategorialSimplex n = record
  { Obj = Fin n
  ; _⇒_ = λ x y → toℕ x ≤ toℕ y
  ; _≈_ = λ _ _ → ⊤
  ; id = ≤-refl
  ; _∘_ = flip ≤-trans
  ; assoc = tt
  ; sym-assoc = tt
  ; identityˡ = tt
  ; identityʳ = tt
  ; identity² = tt
  ; equiv = record { refl = tt ; sym = λ x → tt ; trans = λ x y → tt }
  ; ∘-resp-≈ = λ x y → tt
  }

S-on-Δ : Functor Δ (Cats o ℓ e)
S-on-Δ = record
  { F₀ = λ n → liftC o ℓ e (CategorialSimplex (ℕ.suc n))
  ; F₁ = λ f → fixupF record
    { F₀ = ⟦ f ⟧
    ; F₁ = Δ-monotone f
    ; identity = tt
    ; homomorphism = tt
    ; F-resp-≈ = λ _ → tt
    }
  ; identity = record
    { F⇒G = fixup record { η = λ X → ≤-refl ; commute = λ f → tt ; sym-commute = λ f → tt }
    ; F⇐G = fixup record { η = λ X → ≤-refl ; commute = λ f → tt ; sym-commute = λ f → tt }
    ; iso = λ X → record { isoˡ = lift tt ; isoʳ = lift tt } }
  ; homomorphism = record
    { F⇒G = fixup record { η = λ X → ≤-refl ; commute = λ f → tt ; sym-commute = λ f → tt }
    ; F⇐G = fixup record { η = λ X → ≤-refl ; commute = λ f → tt ; sym-commute = λ f → tt }
    ; iso = λ X → record { isoˡ = lift tt ; isoʳ = lift tt } }
  ; F-resp-≈ = λ x → record
    { F⇒G = fixup record
      { η = λ X → ≤-reflexive (cong toℕ (Δ-pointwise x))
      ; commute = λ f → tt
      ; sym-commute = λ f → tt }
    ; F⇐G = fixup record
      { η = λ X → ≤-reflexive (cong toℕ (sym (Δ-pointwise x)))
      ; commute = λ f → tt
      ; sym-commute = λ f → tt }
    ; iso = λ X → record { isoˡ = lift tt ; isoʳ = lift tt } }
  }
  where
    fixupF : ∀ {C D : Category zero zero zero} → Functor C D → Functor (liftC o ℓ e C) (liftC o ℓ e D)
    fixupF {C} {D} F = liftF o ℓ e D ∘F F ∘F unliftF o ℓ e C
    fixup : ∀ {C D} {F G : Functor C D} → NaturalTransformation F G -> NaturalTransformation (fixupF F) (fixupF G)
    fixup {C} {D} η = liftF o ℓ e D ∘ˡ η ∘ʳ unliftF o ℓ e C

data Spine (C : Category o ℓ e) : ℕ → Category.Obj C  → Category.Obj C  → Set (o ⊔ ℓ) where
  start : (X : Category.Obj C) → Spine C 0 X X
  extend : ∀ {n X Y Z} (f : C [ Y , Z ]) → Spine C n X Y → Spine C (ℕ.suc n) X Z

Nerve : Functor (Cats o ℓ e) (SimplicialSet _ _)
Nerve = Functor.F₀ Precompose (Functor.op S-on-Δ) ∘F (Yoneda.Yoneda.embed (Cats o ℓ e))

Nerve-filler-fun : ∀ (C : Category o ℓ e) {n-1} {k} → Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C → ∀ m → Δ [ m , ℕ.suc n-1 ] → Functor (CategorialSimplex (ℕ.suc m)) C
Nerve-filler-fun C {n-1} {k} horn ℕ.zero f = {!   !}
Nerve-filler-fun C {n-1} {k} horn (ℕ.suc m) f = {!   !}

Nerve-filler : ∀ (C : Category o ℓ e) {n-1} {k} → Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C → _ Functor.F₀ (Functor.F₀ Nerve C) (ℕ.suc n-1)
Nerve-filler C {n-1} {k} horn = ?

Category⇒Nerve : (C : Category o ℓ e) -> Σ ΔSet IsNerve
Category⇒Nerve C = Functor.F₀ Nerve C , record
  { isWeakKanComplex = record
    { filler = {!   !}
    ; filler-cong = {!   !}
    ; is-filler = {!   !}
    }
  ; filler-unique = {!   !} }