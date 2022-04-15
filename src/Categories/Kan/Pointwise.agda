{-# OPTIONS --without-K --safe #-}
module Categories.Kan.Pointwise where

-- Left and Right Kan extensions (known as Lan and Ran)
-- XXX for now there is only Lan

open import Level
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Categories.Category using (Category)
open import Categories.Functor using (_∘F_; Functor) renaming (id to idF)
open import Categories.Functor.Hom using (Hom[_][-,_])
open import Categories.Functor.Profunctor using (Profunctor) renaming (id to idP)
open import Categories.Kan.Preserves using (Preserves-Lan)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

import Categories.Diagram.Cocone.General as Cocones
import Categories.Diagram.Cocone.Weighted as WeightedCocones
import Categories.Diagram.Colimit.General as Colimits
import Categories.Diagram.Colimit.Weighted as WeightedColimits
import Categories.Kan as Ordinary
import Categories.Morphism.Reasoning as MorphismReasoning

private
  variable
    o₀ ℓ₀ e₀ o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ : Level

module _ {A : Category o₀ ℓ₀ e₀} {B : Category o₁ ℓ₁ e₁} {C : Category o₂ ℓ₂ e₂}
           (F : Functor A B) (X : Functor A C) where

  private
    module idP = Profunctor (idP {_} {_} {_} {B})
    module A = Category A
    module B = Category B
    module C = Category C
    module F = Functor F
    module X = Functor X

  open Colimits (idP.app[ F , idF ]) X

  module W (b : B.Obj) = WeightedColimits (Hom[ B ][-, b ] ∘F F.op) X

  record Lan : Set (o₀ ⊔ ℓ₀ ⊔ e₀ ⊔ o₁ ⊔ ℓ₁ ⊔ e₁ ⊔ o₂ ⊔ ℓ₂ ⊔ e₂) where
    field
      colimit : Colimit

    module colimit = Colimit colimit

    ordinary : Ordinary.Lan F X
    ordinary = record
      { L = my-L
      ; η = my-η
      ; σ = my-σ
      ; σ-unique = λ {M α} σ′ commutes′ {b} → {!    !}
      ; commutes = λ M α {a} → let open MorphismReasoning C; open C; open HomReasoning in
        begin
          NaturalTransformation.η α a
        ≈⟨ introˡ (Functor.identity M) ⟩
          Functor.F₁ M B.id ∘ NaturalTransformation.η α a
        ≈˘⟨ colimit.commute {cocone-of M α} {F.₀ a} {a} {lift B.id} ⟩
          NaturalTransformation.η (colimit.rep (cocone-of M α)) (F.₀ a) ∘ (colimit.proj (F.₀ a) a ⟨$⟩ lift B.id)
        ∎
      }
      where
      my-L = colimit.coapex
      module L = Functor my-L
      my-η = ntHelper record
        { η = λ a → colimit.proj (F.₀ a) a ⟨$⟩ lift B.id
        ; commute = λ {X Y} f → let open MorphismReasoning C; open C.HomReasoning; open C in
          begin
            (colimit.proj (F.₀ Y) Y ⟨$⟩ lift B.id) ∘ X.₁ f
          ≈⟨ introˡ L.identity ⟩
            L.₁ B.id ∘ (colimit.proj (F.₀ Y) Y ⟨$⟩ lift B.id) ∘ X.₁ f
          ≈⟨ colimit.colimit-commute B.id f (lift B.id) ⟩
            colimit.proj (F.₀ Y) X ⟨$⟩ lift (B.id B.∘ B.id B.∘ F.₁ f)
          ≈⟨ cong (colimit.proj (F.₀ Y) X) (lift (MorphismReasoning.glueTrianglesʳ B B.identityˡ B.identityˡ)) ⟩
            colimit.proj (F.₀ Y) X ⟨$⟩ lift (F.₁ f)
          ≈˘⟨ cong (colimit.proj (F.₀ Y) X) (lift (MorphismReasoning.elimʳ B (MorphismReasoning.elimʳ B F.identity))) ⟩
            colimit.proj (F.₀ Y) X ⟨$⟩ lift (F.₁ f B.∘ B.id B.∘ F.₁ A.id)
          ≈˘⟨ colimit.colimit-commute (F.₁ f) A.id (lift B.id) ⟩
            L.₁ (F.₁ f) ∘ (colimit.proj (F.₀ X) X ⟨$⟩ lift B.id) ∘ X.₁ A.id
          ≈⟨ refl⟩∘⟨ elimʳ X.identity ⟩
            L.₁ (F.₁ f) ∘ (colimit.proj (F.₀ X) X ⟨$⟩ lift B.id)
          ∎
        }
      cocone-of : ∀ M α → _
      cocone-of M α = record
        { coapex = record
          { ψ = λ b a → record
            { _⟨$⟩_ = λ f → M.₁ (lower f) C.∘ α.η a
            ; cong = λ {i j} i≈j → C.∘-resp-≈ˡ (M.resp-≈ (lower i≈j))
            }
          ; commute = λ g f w → let open MorphismReasoning C; open C.HomReasoning; open C in
            begin
              M.₁ g ∘ (M.₁ (lower w) ∘ α.η _) ∘ X.₁ f
            ≈⟨ refl⟩∘⟨ extendˡ (α.commute f) ⟩
              M.₁ g ∘ (M.₁ (lower w) ∘ M.₁ (F.₁ f)) ∘ α.η _
            ≈˘⟨ refl⟩∘⟨ M.homomorphism ⟩∘⟨refl ⟩
              M.₁ g ∘ M.₁ (lower w B.∘ F.F₁ f) ∘ α.η _
            ≈˘⟨ pushˡ M.homomorphism ⟩
              M.₁ (g B.∘ lower w B.∘ F.₁ f) ∘ α.η _
            ∎
          }
        }
        where
        module M = Functor M
        module α = NaturalTransformation α
      my-σ : ∀ M (α : NaturalTransformation X (M ∘F F)) → NaturalTransformation my-L M
      my-σ M α = colimit.rep (cocone-of M α)
      module σ M α = NaturalTransformation (my-σ M α)

    pointwise : ∀ b → W.Colimit b
    pointwise b = record
      { initial = record
        { ⊥ = record
          { coapex = record
            { ψ = λ a → record
              { _⟨$⟩_ = λ f → colimit.proj b a ⟨$⟩ lift f
              ; cong = λ eq → cong (colimit.proj b a) (lift eq) }
            ; commute = λ {a a′} f w → let open MorphismReasoning C; open C.HomReasoning; open C in
              begin
                (colimit.proj b a′ ⟨$⟩ lift w) ∘ X.₁ f
              ≈⟨ introˡ (Functor.identity colimit.coapex) ⟩
                Functor.F₁ colimit.coapex B.id ∘ (colimit.proj b a′ ⟨$⟩ lift w) ∘ X.₁ f
              ≈⟨ colimit.colimit-commute B.id f (lift w) ⟩
                colimit.proj b a ⟨$⟩ lift (B.id B.∘ w B.∘ F.₁ f)
              ∎
            }
          }
        ; ⊥-is-initial = record
          { ! = λ {κ} → record
            { arr = NaturalTransformation.η (colimit.rep (pointwise-cocone κ)) b ; commute = {!   !} }
          ; !-unique = {!   !}
          }
        }
      }
      where
      pointwise-cocone : ∀ κ → _
      pointwise-cocone κ = record
        { N = {!   !}
        ; coapex = record
          { ψ = λ b′ a → record { _⟨$⟩_ = {!λ w → WeightedCocones.Cocone.ψ κ a ⟨$⟩_  !} ; cong = {!   !} }
          ; commute = {!   !}
          }
        }

    -- XXX show they are preserved by representable functors -- should be preserved strongly!

    open Ordinary.Lan ordinary public

  pointwise-if-preserved : (ℓ₁ ≡ ℓ₂) → (e₁ ≡ e₂) → (L : Ordinary.Lan F X) → (∀ c → Preserves-Lan (Functor.op Hom[ C ][-, c ]) L) → Lan
  pointwise-if-preserved (_≡_.refl) (_≡_.refl) L elongs = record
    { colimit = record
      { initial = record
        { ⊥ = record
          { N = L.L
          ; coapex = record
            { ψ = λ b a → record { _⟨$⟩_ = λ w → L.L.₁ (lower w) C.∘ L.η.η a
            ; cong = λ eq → C.∘-resp-≈ˡ (L.L.resp-≈ (lower eq))
            }
          ; commute = λ g f w → let open C; open HomReasoning; open MorphismReasoning C in
            begin
              L.L.₁ g ∘ (L.L.₁ (lower w) ∘ L.η.η _) ∘ X.₁ f
            ≈⟨ pushʳ (extendˡ (L.η.commute f)) ⟩
              (L.L.₁ g ∘ L.L.₁ (lower w) ∘ L.L.₁ (F.₁ f)) ∘ L.η.η _
            ≈⟨ glueTrianglesʳ (Equiv.sym L.L.homomorphism) (Equiv.sym L.L.homomorphism) ⟩∘⟨refl ⟩
              L.L.₁ ((g B.∘ lower w) B.∘ F.₁ f) ∘ L.η.η _
            ≈⟨ L.L.resp-≈ B.assoc ⟩∘⟨refl ⟩
              L.L.₁ (g B.∘ lower w B.∘ F.₁ f) ∘ L.η.η _
            ∎ }
          }
        ; ⊥-is-initial = record
          { ! = λ {κ} → let module κ = Cocones.Cocone κ in record
            { arr = {!L.σ Cocones.Cocone N    !}
            ; commute = {!   !} }
          ; !-unique = {!   !}
          }
        }
      }
    }
    where
    module L = Ordinary.Lan L
    module elongs c = Ordinary.IsLan (elongs c)