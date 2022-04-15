{-# OPTIONS --without-K --safe #-}

module Categories.Kan.Preserves where

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; associator)
open import Categories.Kan

private
  variable
    o ℓ e : Level
    A B C D E : Category o ℓ e
    F G : Functor C D

module _ {F : Functor A B} {X : Functor A C} where
  private
    module F = Functor F
    module X = Functor X

  Preserves-Lan : ∀ (G : Functor C D) (L : Lan F X) → Set _
  Preserves-Lan G L = IsLan F (G ∘F X) (G ∘F Lan.L L) (NaturalIsomorphism.F⇐G (associator F (Lan.L L) G) ∘ᵥ (G ∘ˡ Lan.η L))

  Preserves-Ran : ∀ (G : Functor C D) (R : Ran F X) → Set _
  Preserves-Ran G R = IsRan F (G ∘F X) (G ∘F Ran.R R) ((G ∘ˡ Ran.ε R) ∘ᵥ NaturalIsomorphism.F⇒G (associator F (Ran.R R) G))