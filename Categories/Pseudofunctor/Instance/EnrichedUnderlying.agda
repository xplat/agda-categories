{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Pseudofunctor.Instance.EnrichedUnderlying
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) (v : Level) where

-- The "forgetful" functor from V-enriched categories to their
-- underlying Setoid-categories.

open import Data.Product as Prod using (_,_)

open import Categories.Bicategory.Instance.Cats
open import Categories.Bicategory.Instance.EnrichedCats M
open import Categories.Enriched.Category M
open import Categories.Enriched.Functor M
open import Categories.Enriched.NaturalTransformation M
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Pseudofunctor using (Pseudofunctor)

private
  module V = Setoid-Category V
  module UnderlyingReasoning {c} (C : Category c) where
    open Underlying C public hiding (id)
    open HomReasoning public
  open NaturalTransformation using (_[_])

  -- Aliases used to shorten some proof expressions

  module UF = UnderlyingFunctor
  infixr 14 _$₀_ _$₁_
  _$₀_ = UF.F₀
  _$₁_ = UF.F₁

-- The "forgetful" pseudofunctor mapping a V-enriched category to its
-- underlying Setoid-category.
--
-- Note that all the equational reasoning happens in the underlying
-- (ordinary) categories!

EnrichedUnderlying : Pseudofunctor (EnrichedCats v) (Cats v ℓ e)
EnrichedUnderlying = record
  { P₀ = underlying
  ; P₁ = record
    { F₀ = underlyingFunctor
    ; F₁ = underlyingNT
    ; identity     = V.Equiv.refl
    ; homomorphism = V.Equiv.refl
    ; F-resp-≈     = λ eq → eq
    }
  ; P-identity = λ {C} →
    let module C = Underlying C
        open UnderlyingReasoning C
    in niHelper record
      { η = λ _ → ntHelper record
        { η       = λ _ → C.id
        ; commute = λ f → begin
            C.id ∘ f              ≈⟨ identityˡ ⟩
            f                     ≈˘⟨ identityʳ ○ V.identityˡ ⟩
            (V.id V.∘ f) ∘ C.id   ∎
        }
      ; η⁻¹ = λ _ → ntHelper record
        { η       = λ _ → C.id
        ; commute = λ f → begin
            C.id ∘ (V.id V.∘ f)   ≈⟨ identityˡ ○ V.identityˡ ⟩
            f                     ≈˘⟨ identityʳ ⟩
            f ∘ C.id              ∎
        }
      ; commute = λ _ → V.Equiv.refl
      ; iso     = λ _ → record { isoˡ = C.identityˡ ; isoʳ = C.identityʳ }
      }
  ; P-homomorphism = λ {C D E} →
    let module C = Underlying C
        module D = Underlying D
        module E = Underlying E
        open UnderlyingReasoning E
    in niHelper record
      { η = λ{ (F , G) → ntHelper record
        { η       = λ _ → E.id
        ; commute = λ f → begin
            E.id ∘ F $₁ G $₁ f     ≈⟨ identityˡ ⟩
            F $₁ G $₁ f            ≈˘⟨ V.assoc ⟩
            (F ∘F G) $₁ f          ≈˘⟨ identityʳ ⟩
            (F ∘F G) $₁ f ∘ E.id   ∎
        } }
      ; η⁻¹ = λ{ (F , G) → ntHelper record
        { η       = λ _ → E.id
        ; commute = λ f → begin
            E.id ∘ (F ∘F G) $₁ f   ≈⟨ identityˡ ⟩
            (F ∘F G) $₁ f          ≈⟨ V.assoc ⟩
            F $₁ G $₁ f            ≈˘⟨ identityʳ ⟩
            F $₁ G $₁ f ∘ E.id     ∎
        } }
      ; commute = λ{ {F , G} {H , I} (α , β) {X} → begin
          E.id ∘ H $₁ β [ X ] ∘ α [ G $₀ X ]     ≈⟨ identityˡ ⟩
          H $₁ β [ X ] ∘ α [ G $₀ X ]            ≈˘⟨ identityʳ ⟩
          (H $₁ β [ X ] ∘ α [ G $₀ X ]) ∘ E.id   ∎ }
      ; iso     = λ _ → record { isoˡ = E.identityˡ ; isoʳ = E.identityʳ }
      }
  ; unitaryˡ = λ {_ D} →
    let module D = Underlying D
        open UnderlyingReasoning D
    in begin
      D.id ∘ D.id ∘ (V.id V.∘ D.id) ∘ D.id   ≈⟨ identityˡ ○ identityˡ ⟩
      (V.id V.∘ D.id) ∘ D.id                 ≈⟨ identityʳ ○ V.identityˡ ⟩
      D.id                                   ∎
  ; unitaryʳ = λ {C D F X} →
    let module C = Underlying C
        module D = Underlying D
        open UnderlyingReasoning D
    in begin
      D.id ∘ D.id ∘ F $₁ C.id ∘ D.id   ≈⟨ identityˡ ○ identityˡ ○ identityʳ ⟩
      F $₁ C.id                        ≈⟨ UF.identity F ⟩
      D.id                             ∎
  ; assoc = λ {_ B C D F G H X} →
    let module B = Underlying B
        module C = Underlying C
        module D = Underlying D
        open UnderlyingReasoning D
    in begin
      D.id ∘ D.id ∘ (H ∘F G) $₁ B.id ∘ D.id  ≈⟨ identityˡ ⟩
      D.id ∘ (H ∘F G) $₁ B.id ∘ D.id         ≈⟨ refl⟩∘⟨ V.assoc ⟩∘⟨refl ⟩
      D.id ∘ H $₁ G $₁ B.id ∘ D.id           ≈⟨ refl⟩∘⟨ UF.F-resp-≈ H
                                                  (UF.identity G) ⟩∘⟨refl ⟩
      D.id ∘ (H $₁ C.id) ∘ D.id              ≈˘⟨ refl⟩∘⟨ identityʳ ⟩∘⟨refl ⟩
      D.id ∘ (H $₁ C.id ∘ D.id) ∘ D.id       ∎
  }
