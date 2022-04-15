{-# OPTIONS --without-K --safe #-}
open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Category.Instance.Setoids

-- Also defines the category of cocones "over a Functor F"

module Categories.Category.Construction.Cocones.Weighted
  {o ℓ e} {o′ ℓ′ e′} {ℓ″ e″} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (W : Functor (Category.op J) (Setoids ℓ″ e″)) (F : Functor J C) where

open Category C

private
  module W = Functor W
  variable
    X : Obj

open HomReasoning
open Functor F
open import Data.Product
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Categories.Morphism as Mor
import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.Diagram.Cocone.Weighted W F public

open Mor C
open IsoEquiv C
open import Categories.Morphism.Reasoning C
open Cocone
open Coapex
open Cocone⇒
open Equiv

Cocones : Category _ _ _
Cocones = record
  { Obj       = Cocone
  ; _⇒_       = Cocone⇒
  ; _≈_       = λ f g → arr f ≈ arr g
  ; id        = record { arr = id ; commute = identityˡ }
  ; _∘_       = λ {A B C} f g → record
    { arr     = arr f ∘ arr g
    ; commute = λ {X} {XX} → begin
      (arr f ∘ arr g) ∘ (ψ A X ⟨$⟩ XX) ≈⟨ pullʳ (commute g) ⟩
      arr f ∘ (ψ B X ⟨$⟩ XX)           ≈⟨ commute f ⟩
      ψ C X ⟨$⟩ XX                     ∎
    }
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

module Cocones = Category Cocones

private
  variable
    K K′ : Cocone
  module CM = Mor Cocones
  module CI = IsoEquiv Cocones

open CM using () renaming (_≅_ to _⇔_)
open CI using () renaming (_≃_ to _↮_)

cocone-resp-iso : ∀ (κ : Cocone) → Cocone.N κ ≅ X → Σ[ κ′ ∈ Cocone ] κ ⇔ κ′
cocone-resp-iso {X = X} κ κ≅X = record
  { coapex = record
    { ψ       = λ Y → record
      { _⟨$⟩_ = λ YY → from ∘ (Cocone.ψ κ Y ⟨$⟩ YY)
      ; cong = λ eq → ∘-resp-≈ʳ (cong (Cocone.ψ κ Y) eq) }
    ; commute = λ f YY → pullʳ (Cocone.commute κ f YY)
    }
  } , record
  { from = record
    { arr     = from
    ; commute = refl
    }
  ; to   = record
    { arr     = to
    ; commute = cancelˡ isoˡ
    }
  ; iso  = record
    { isoˡ    = isoˡ
    ; isoʳ    = isoʳ
    }
  }
  where open _≅_ κ≅X
        open Cocone
        open Coapex

iso-cocone⇒iso-coapex : K ⇔ K′ → N K ≅ N K′
iso-cocone⇒iso-coapex K⇔K′ = record
  { from = arr from
  ; to   = arr to
  ; iso  = record
    { isoˡ = isoˡ
    ; isoʳ = isoʳ
    }
  }
  where open _⇔_ K⇔K′
