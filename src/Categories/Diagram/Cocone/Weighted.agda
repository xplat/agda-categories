{-# OPTIONS --without-K --safe #-}
open import Relation.Binary using (module Setoid)
open import Function.Equality using (_⟶_; _⟨$⟩_)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Category.Instance.Setoids

-- Cocone over a Functor F (from shape category J into category C) with weight W

module Categories.Diagram.Cocone.Weighted
  {o ℓ e} {o′ ℓ′ e′} {ℓ″ e″} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (W : Functor (Category.op J) (Setoids ℓ″ e″)) (F : Functor J C) where

private
  module W = Functor W
open Category C
open Functor F

open import Level

record Coapex (N : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ ℓ″ ⊔ e″) where
  field
    ψ       : (X : Category.Obj J) → W.₀ X ⟶ hom-setoid {F₀ X} {N}
    commute : ∀ {X Y} (f : J [ X , Y ]) (YY : Setoid.Carrier (W.₀ Y)) → (ψ Y ⟨$⟩ YY) ∘ F₁ f ≈ ψ X ⟨$⟩ (W.₁ f ⟨$⟩ YY)

record Cocone : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ ℓ″ ⊔ e″) where
  field
    {N}    : Obj
    coapex : Coapex N

  open Coapex coapex public

open Coapex
open Cocone

record Cocone⇒ (c c′ : Cocone) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ″) where
  field
    arr     : N c ⇒ N c′
    commute : ∀ {X} {XX} → arr ∘ (ψ c X ⟨$⟩ XX) ≈ ψ c′ X ⟨$⟩ XX

open Cocone⇒
