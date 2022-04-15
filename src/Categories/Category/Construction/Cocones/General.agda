{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Profunctor hiding (id)
open import Categories.Category.Instance.Setoids

-- Also defines the category of cocones "over a Functor F"

module Categories.Category.Construction.Cocones.General
  {o ℓ e} {o′ ℓ′ e′} {o″ ℓ″ e″} {ℓ‴ e‴} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {K : Category o″ ℓ″ e″} (W : Profunctor ℓ‴ e‴ K J) (F : Functor J C) where

open Category C

private
  module W = Profunctor W
  variable
    X : Functor K C

open HomReasoning
open Functor F
open import Data.Product
open import Data.Sum using (inj₁; inj₂)
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Categories.Morphism as Mor
import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.NaturalTransformation using (_∘ᵥ_; NaturalTransformation) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Diagram.Cocone.General W F public

open Mor C
open IsoEquiv C hiding (_≃_)
open import Categories.Morphism.Reasoning C
open Cocone
open Coapex
open Cocone⇒
open Equiv

Cocones : Category _ _ _
Cocones = record
  { Obj       = Cocone
  ; _⇒_       = Cocone⇒
  ; _≈_       = λ f g → arr f ≃ arr g
  ; id        = record { arr = idN ; commute = identityˡ }
  ; _∘_       = λ {A B C} f g → record
    { arr     = arr f ∘ᵥ arr g
    ; commute = λ {k} {X} {XX} →
        begin
          (NaturalTransformation.η (arr f) k ∘ NaturalTransformation.η (arr g) k) ∘ (ψ A k X ⟨$⟩ XX)
        ≈⟨ pullʳ (commute g) ⟩
          NaturalTransformation.η (arr f) k ∘ (ψ B k X ⟨$⟩ XX)
        ≈⟨ commute f ⟩
          ψ C k X ⟨$⟩ XX
        ∎
    }
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = refl
    ; sym   = λ f → sym f
    ; trans = λ f g → trans f g
    }
  ; ∘-resp-≈  = λ f g → ∘-resp-≈ f g
  }

module Cocones = Category Cocones

private
  variable
    κ κ′ : Cocone
  module CM = Mor Cocones
  module CI = IsoEquiv Cocones

open CM using () renaming (_≅_ to _⇔_)
open CI using () renaming (_≃_ to _↮_)

cocone-resp-iso : ∀ (κ : Cocone) → NaturalIsomorphism (Cocone.N κ) X → Σ[ κ′ ∈ Cocone ] κ ⇔ κ′
cocone-resp-iso {X = X} κ κ≅X = record
  { coapex = record
    { ψ       = λ k Y → record
      { _⟨$⟩_ = λ YY → NaturalTransformation.η F⇒G k ∘ (Cocone.ψ κ k Y ⟨$⟩ YY)
      ; cong = λ eq → ∘-resp-≈ʳ (cong (Cocone.ψ κ k Y) eq) }
    ; commute = λ {A B} g {Z Y} f YY → let module X = Functor X in
      begin
        X.₁ g ∘ (⇒.η A ∘ (ψ κ A Y ⟨$⟩ YY)) ∘ F₁ f
      ≈˘⟨ extendʳ (pushˡ (⇒.commute g)) ⟩
        (⇒.η B ∘ Functor.F₁ (N κ) g) ∘ ((ψ κ A Y ⟨$⟩ YY) ∘ F₁ f)
      ≈⟨ pullʳ (Cocone.commute κ g f YY) ⟩
        ⇒.η B ∘ (ψ κ B Z ⟨$⟩ (W.F₁ (f , g) ⟨$⟩ YY))
      ∎
    }
  } , record
  { from = record
    { arr     = F⇒G
    ; commute = refl
    }
  ; to   = record
    { arr     = F⇐G
    ; commute = cancelˡ (Iso.isoˡ (iso _))
    }
  ; iso  = record
    { isoˡ    = Iso.isoˡ (iso _)
    ; isoʳ    = Iso.isoʳ (iso _)
    }
  }
  where open NaturalIsomorphism κ≅X
        open Cocone
        open Coapex

iso-cocone⇒iso-coapex : κ ⇔ κ′ → NaturalIsomorphism (N κ) (N κ′)
iso-cocone⇒iso-coapex K⇔K′ = record
  { F⇒G  = arr from
  ; F⇐G  = arr to
  ; iso  = λ X → record
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where open _⇔_ K⇔K′

CoconeExs : Category _ _ _
CoconeExs = record
  { Obj = CoconeEx
  ; _⇒_ = CoconeEx⇒
  ; _≈_ = λ f g → CoconeEx⇒.arr f ≃ CoconeEx⇒.arr g
  ; id = record { arr = idN ; commute = identityʳ }
  ; _∘_ = λ {A B C} f g → record
    { arr = CoconeEx⇒.arr f ∘ᵥ CoconeEx⇒.arr g
    ; commute = λ {j} → glueTrianglesʳ (CoconeEx⇒.commute f) (CoconeEx⇒.commute g) }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = refl ; sym = λ eq → sym eq ; trans = λ eq₁ eq₂ → trans eq₁ eq₂ }
  ; ∘-resp-≈ = λ eq₁ eq₂ → ∘-resp-≈ eq₁ eq₂
  }

Cocones-to-CoconeExs : Functor Cocones CoconeExs
Cocones-to-CoconeExs = record
  { F₀ = Cocone-as-CoconeEx
  ; F₁ = Cocone⇒-as-CoconeEx⇒
  ; identity = λ { {_} {inj₁ x} → refl ; {_} {inj₂ y} → refl }
  ; homomorphism = λ { {x = inj₁ j} → sym identity² ; {x = inj₂ k} → refl }
  ; F-resp-≈ = λ eq → λ { {inj₁ j} → refl ; {inj₂ k} → eq }
  }

CoconeExs-to-Cocones : Functor CoconeExs Cocones
CoconeExs-to-Cocones = record
  { F₀ = CoconeEx-as-Cocone
  ; F₁ = CoconeEx⇒-as-Cocone⇒
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ eq → eq
  }

-- XXX complete proof that this is an (adjoint?) equivalence of categories