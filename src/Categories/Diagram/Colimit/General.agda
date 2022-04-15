{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Profunctor hiding (id)
open import Categories.Category.Instance.Setoids

-- Colimit of a Functor F : J → C weighted by W : K ⇸ J
module Categories.Diagram.Colimit.General
  {o ℓ e} {o′ ℓ′ e′} {o″ ℓ″ e″} {ℓ‴ e‴} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {K : Category o″ ℓ″ e″} (W : Profunctor ℓ‴ e‴ K J) (F : Functor J C) where

private
  module C = Category C
  module J = Category J
  module K = Category K
  module W = Profunctor W
open C
open HomReasoning
open Equiv
open Functor F

open import Level
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary using (module Setoid)

open import Categories.Category.Construction.Cocones.General W F renaming (Cocone⇒ to _⇨_)
open import Categories.Object.Initial as I hiding (up-to-iso; transport-by-iso)
open import Categories.Kan using (Lan)
open import Categories.Morphism.Reasoning C
open import Categories.Morphism C
open import Categories.Morphism Cocones as MC using () renaming (_≅_ to _⇔_)
open import Categories.NaturalTransformation using (_∘ᵥ_; _∘ʳ_; NaturalTransformation) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

private
  variable
    κ κ′  : Cocone
    A B   : J.Obj
    S T   : K.Obj
    AA    : Setoid.Carrier (W.₀ (A , S))
    X Y Z : Functor K C
    q     : κ ⇨ κ′

-- A Colimit is an Initial object in the category of Cocones
--   (This could be unpacked...)
record Colimit : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″ ⊔ ℓ‴ ⊔ e‴) where
  field
    initial : Initial Cocones

  module initial = Initial initial

  open initial using () renaming (⊥ to colimit) public
  open Cocone colimit hiding (coapex) renaming (N to coapex; ψ to proj; commute to colimit-commute) public

  rep-cocone : ∀ κ → colimit ⇨ κ
  rep-cocone κ = initial.! {κ}

  rep : ∀ κ → NaturalTransformation coapex (Cocone.N κ)
  rep κ = arr
    where open _⇨_ (rep-cocone κ)

  unrep : NaturalTransformation coapex X → Cocone
  unrep {X = X} f = record {
    coapex        = record
      { ψ       = λ S A → record
        { _⟨$⟩_ = λ AA → NaturalTransformation.η f S ∘ (proj S A ⟨$⟩ AA)
        ; cong  = λ eq → ∘-resp-≈ʳ (cong (proj S A) eq)
        }
      ; commute = λ h g YY → let module X = Functor X in
        begin
          X.₁ h ∘ (NaturalTransformation.η f _ ∘ (proj _ _ ⟨$⟩ YY)) ∘ F₁ g
        ≈˘⟨ extendʳ (pushˡ (NaturalTransformation.commute f h)) ⟩
          (NaturalTransformation.η f _ ∘ Functor.F₁ coapex h) ∘ ((proj _ _ ⟨$⟩ YY) ∘ F₁ g)
        ≈⟨ pullʳ (colimit-commute h g YY) ⟩
          NaturalTransformation.η f _ ∘ (proj _ _ ⟨$⟩ (W.F₁ (g , h) ⟨$⟩ YY))
        ∎
      }
    }

  coconify : (f : NaturalTransformation coapex X) → colimit ⇨ unrep f
  coconify f = record
    { arr     = f
    ; commute = refl
    }

  commute : NaturalTransformation.η (rep κ) S ∘ (proj S A ⟨$⟩ AA) ≈ Cocone.ψ κ S A ⟨$⟩ AA
  commute {κ = κ} = _⇨_.commute (rep-cocone κ)

  unrep-cone : (colimit ⇨ κ) → Cocone
  unrep-cone f = unrep (_⇨_.arr f)

  g-η : ∀ {f : NaturalTransformation coapex X} → rep (unrep f) ≃ f
  g-η {f = f} = initial.!-unique (coconify f)

  η-cocone : Cocones [ rep-cocone colimit ≈ Category.id Cocones ]
  η-cocone = initial.⊥-id (rep-cocone colimit)

  η : rep colimit ≃ idN
  η = η-cocone

  rep-cocone∘ : Cocones [ Cocones [ q ∘ rep-cocone κ ] ≈ rep-cocone κ′ ]
  rep-cocone∘ {κ = κ} {q = q} = Equiv.sym (initial.!-unique (Cocones [ q ∘ rep-cocone κ ]))

  rep∘ : ∀ {q : κ ⇨ κ′} → _⇨_.arr q ∘ᵥ rep κ ≃ rep κ′
  rep∘ {q = q} = rep-cocone∘ {q = q}

  rep-cone-self-id : Cocones [ rep-cocone colimit ≈  Cocones.id  ]
  rep-cone-self-id = initial.!-unique ( Cocones.id )

  rep-self-id : rep colimit ≃ idN
  rep-self-id = rep-cone-self-id

record ColimitEx : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″ ⊔ ℓ‴ ⊔ e‴) where
  field
    initial : Initial CoconeExs

  module initial = Initial initial

  open initial using () renaming (⊥ to colimit) public

Colimit-as-ColimitEx : Colimit → ColimitEx
Colimit-as-ColimitEx κ = record
  { initial = record
    { ⊥ = Cocone-as-CoconeEx (Colimit.colimit κ)
    ; ⊥-is-initial = record
      { ! = Cocone⇒-as-CoconeEx⇒′ (Colimit.initial.! κ)
      ; !-unique = λ {x} f → λ
        { {inj₁ j} → sym (flip-fromˡ (CoconeEx.pin.FX≅GX x) (CoconeEx⇒.commute f))
        ; {inj₂ k} → Colimit.initial.!-unique κ (CoconeEx⇒-as-Cocone⇒″ f)
        }
      }
    }
  }

ColimitEx-as-Colimit : ColimitEx → Colimit
ColimitEx-as-Colimit x = record
  { initial = record
    { ⊥ = CoconeEx-as-Cocone (ColimitEx.colimit x)
    ; ⊥-is-initial = record
      { ! = CoconeEx⇒-as-Cocone⇒′ (ColimitEx.initial.! x)
      ; !-unique = λ {κ} f {k} → ColimitEx.initial.!-unique x (Cocone⇒-as-CoconeEx⇒″ f) } } }

pinned-down : ∀ M → NaturalTransformation F (M ∘F W.cograph.Inj₁) → CoconeEx
pinned-down M μ = record
  { extension = record
    { F₀ = λ { (inj₁ j) → F₀ j ; (inj₂ k) → M.₀ (inj₂ k) }
    ; F₁ = λ
      { {inj₁ j} {inj₁ j′} f → F₁ (lower f)
      ; {inj₁ j} {inj₂ k} f → M.₁ f ∘ μ.η j
      ; {inj₂ k} {inj₂ k′} f → M.₁ f
      }
    ; identity = λ { {inj₁ j} → identity ; {inj₂ k} → M.identity }
    ; homomorphism = λ
      { {inj₁ X} {inj₁ Y} {inj₁ Z} {f} {g} → homomorphism
      ; {inj₁ X} {inj₁ Y} {inj₂ Z} {f} {g} → begin
          M.₁ (W.cograph [ g ∘ f ]) ∘ μ.η X
        ≈⟨ M.homomorphism ⟩∘⟨refl ⟩
          (M.₁ g ∘ M.₁ f) ∘ μ.η X
        ≈⟨ extendˡ (μ.sym-commute (lower f)) ⟩
          (M.₁ g ∘ μ.η Y) ∘ F₁ (lower f)
        ∎
      ; {inj₁ X} {inj₂ Y} {inj₂ Z} {f} {g} → pushˡ M.homomorphism
      ; {inj₂ X} {inj₂ Y} {inj₂ Z} {f} {g} → M.homomorphism
      }
    ; F-resp-≈ = λ
      { {inj₁ X} {inj₁ Y} {f} {g} eq → F-resp-≈ (lower eq)
      ; {inj₁ X} {inj₂ Y} {f} {g} eq → ∘-resp-≈ˡ (M.resp-≈ eq)
      ; {inj₂ X} {inj₂ Y} {f} {g} eq → M.resp-≈ eq
      }
    }
  ; pin = record
    { F⇒G = record
      { η = λ j → id
      ; commute = NaturalTransformation.commute {F = F} idN
      ; sym-commute = NaturalTransformation.sym-commute {F = F} idN
      }
    ; F⇐G = record
      { η = λ j → id
      ; commute = NaturalTransformation.commute {F = F} idN
      ; sym-commute = NaturalTransformation.sym-commute {F = F} idN
      }
    ; iso = λ j → record { isoˡ = identity² ; isoʳ = identity² }
    }
  }
  where
  module M = Functor M
  module μ = NaturalTransformation μ

pin-down : ∀ M (μ : NaturalTransformation F (M ∘F W.cograph.Inj₁)) → NaturalTransformation (CoconeEx.extension (pinned-down M μ)) M
pin-down M μ = record
  { η = λ { (inj₁ j) → μ.η j ; (inj₂ k) → id }
  ; commute = λ
    { {inj₁ X} {inj₁ Y} f → μ.commute (lower f)
    ; {inj₁ X} {inj₂ Y} f → identityˡ
    ; {inj₂ X} {inj₂ Y} f → id-comm-sym
    }
  ; sym-commute = λ
    { {inj₁ X} {inj₁ Y} f → μ.sym-commute (lower f)
    ; {inj₁ X} {inj₂ Y} f → Equiv.sym identityˡ
    ; {inj₂ X} {inj₂ Y} f → id-comm
    }
  }
  where module μ = NaturalTransformation μ

ColimitEx-as-Lan : ColimitEx → Lan W.cograph.Inj₁ F
ColimitEx-as-Lan x = record
  { L = CoconeEx.extension x.colimit
  ; η = CoconeEx.pin.F⇐G x.colimit
  ; σ = λ M μ → pin-down M μ ∘ᵥ CoconeEx⇒.arr x.initial.!
  ; σ-unique = λ {M μ} σ′ μ≃σ′∘η → λ
    { {inj₁ j} →
      let !M = x.initial.! {pinned-down M μ} in
      begin
        NaturalTransformation.η σ′ (inj₁ j)
      ≈⟨ switch-tofromʳ (CoconeEx.pin.FX≅GX x.colimit) (sym μ≃σ′∘η) ⟩
        NaturalTransformation.η μ j ∘ CoconeEx.pin.⇒.η x.colimit j
      ≈˘⟨ refl⟩∘⟨ CoconeEx⇒.commute !M ⟩
        NaturalTransformation.η μ j ∘ id ∘ NaturalTransformation.η (CoconeEx⇒.arr !M) (inj₁ j)
      ≈⟨ refl⟩∘⟨ identityˡ ⟩
        NaturalTransformation.η μ j ∘ NaturalTransformation.η (CoconeEx⇒.arr !M) (inj₁ j)
      ∎
    ; {inj₂ k} →
      let !M = x.initial.! {pinned-down M μ} in
      begin
        NaturalTransformation.η σ′ (inj₂ k)
      ≈˘⟨ x.initial.!-unique (tether M μ σ′ μ≃σ′∘η) ⟩
        CoconeEx⇒.arr.η !M (inj₂ k)
      ≈˘⟨ identityˡ ⟩
        id ∘ CoconeEx⇒.arr.η !M (inj₂ k)
      ∎
    }
  ; commutes = λ M μ {j} → insertʳ let !M = x.initial.! {pinned-down M μ} in
    begin
      CoconeEx⇒.arr.η !M (inj₁ j) ∘ CoconeEx.pin.⇐.η x.colimit j
    ≈⟨ introˡ Equiv.refl ⟩∘⟨refl ⟩
      (id ∘ CoconeEx⇒.arr.η !M (inj₁ j)) ∘ _
    ≈⟨ CoconeEx⇒.commute (x.initial.! {pinned-down M μ}) ⟩∘⟨refl ⟩
      CoconeEx.pin.⇒.η x.colimit j ∘ CoconeEx.pin.⇐.η x.colimit j
    ≈⟨ CoconeEx.pin.iso.isoʳ x.colimit j ⟩
      id
    ∎ }
  where
  module x = ColimitEx x
  tether : ∀ M μ (σ′ : NaturalTransformation (CoconeEx.extension x.colimit) M) → μ ≃ (σ′ ∘ʳ W.cograph.Inj₁) ∘ᵥ CoconeEx.pin.F⇐G x.colimit → CoconeEx⇒ x.colimit (pinned-down M μ)
  tether M μ σ′ eq = record
    { arr = record
      { η = λ { (inj₁ j) → CoconeEx.pin.⇒.η x.colimit j ; (inj₂ k) → NaturalTransformation.η σ′ (inj₂ k) }
      ; commute = λ
        { {inj₁ X} {inj₁ Y} f → CoconeEx.pin.⇒.commute x.colimit (lower f)
        ; {inj₁ X} {inj₂ Y} f →
          begin
            σ′.η (inj₂ Y) ∘ colim.extension.₁ f
          ≈⟨ σ′.commute f ⟩
            M.₁ f ∘ σ′.η (inj₁ X)
          ≈˘⟨ pullʳ (flip-iso (≅.sym colim.pin.FX≅GX) eq) ⟩
            (M.₁ f ∘ μ.η X) ∘ colim.pin.⇒.η X
          ∎
        ; {inj₂ X} {inj₂ Y} f → NaturalTransformation.commute σ′ f
        }
      ; sym-commute = λ
        { {inj₁ X} {inj₁ Y} f → CoconeEx.pin.⇒.sym-commute x.colimit (lower f)
        ; {inj₁ X} {inj₂ Y} f →
          begin
            (M.₁ f ∘ μ.η X) ∘ colim.pin.⇒.η X
          ≈⟨ pullʳ (flip-iso (≅.sym colim.pin.FX≅GX) eq) ⟩
            M.₁ f ∘ σ′.η (inj₁ X)
          ≈⟨ σ′.sym-commute f ⟩
            σ′.η (inj₂ Y) ∘ colim.extension.₁ f
          ∎
        ; {inj₂ X} {inj₂ Y} f → NaturalTransformation.sym-commute σ′ f
        }
      }
    ; commute = identityˡ }
    where
    module M = Functor M
    module μ = NaturalTransformation μ
    module σ′ = NaturalTransformation σ′
    module colim = CoconeEx x.colimit

Lan-as-ColimitEx : Lan W.cograph.Inj₁ F → ColimitEx
Lan-as-ColimitEx L = record
  { initial = record
    { ⊥ = my-⊥
    ; ⊥-is-initial = record
      { ! = λ {X} → let module X = CoconeEx X in record
        { arr = L.σ X.extension X.pin.F⇐G
        ; commute = λ {j} → sym (switch-tofromˡ X.pin.FX≅GX (sym (switch-tofromʳ my-⊥.pin.FX≅GX (sym (L.commutes X.extension X.pin.F⇐G)))))
        }
      ; !-unique = λ {X} f → let module X = CoconeEx X ; module f = CoconeEx⇒ f in Equiv.sym (L.σ-unique {X.extension} {X.pin.F⇐G} f.arr (λ {j} → Equiv.sym (f.commute-other {j})))
      }
    }
  }
  where
  module L = Lan L
  module Pinned = CoconeEx (pinned-down L.L L.η)

  my-⊥ : CoconeEx
  my-⊥ = record
    { extension = L.L
    ; pin = record
      { F⇒G = let module it = NaturalTransformation (L.σ Pinned.extension Pinned.pin.F⇐G ∘ʳ W.cograph.Inj₁) in
        record { η = it.η ; commute = it.commute ; sym-commute = it.sym-commute }
      ; F⇐G = L.η
      ; iso = λ j → record
        { isoˡ =
          begin
            L.η.η j ∘ NaturalTransformation.η (L.σ Pinned.extension Pinned.pin.F⇐G) (inj₁ j)
          ≈⟨ L.σ-unique {L.L} {L.η} (pin-down L.L L.η ∘ᵥ (L.σ Pinned.extension Pinned.pin.F⇐G)) (insertʳ (Equiv.sym (L.commutes Pinned.extension Pinned.pin.F⇐G))) ⟩
            NaturalTransformation.η (L.σ L.L L.η) (inj₁ j)
          ≈˘⟨ L.σ-unique {L.L} {L.η} idN (Equiv.sym identityˡ) ⟩
            id
          ∎
        ; isoʳ = Equiv.sym (L.commutes Pinned.extension Pinned.pin.F⇐G)
        }
      }
    }
  module my-⊥ = CoconeEx my-⊥

open Colimit

up-to-iso-cone : (L₁ L₂ : Colimit) → colimit L₁ ⇔ colimit L₂
up-to-iso-cone L₁ L₂ =  I.up-to-iso Cocones (initial L₁) (initial L₂)

up-to-iso : (L₁ L₂ : Colimit) → NaturalIsomorphism (coapex L₁) (coapex L₂)
up-to-iso L₁ L₂ =  iso-cocone⇒iso-coapex (up-to-iso-cone L₁ L₂)

transport-by-iso-cocone : (C : Colimit) → colimit C ⇔ κ → Colimit
transport-by-iso-cocone C C⇿K = record
  { initial =  I.transport-by-iso Cocones (initial C) C⇿K
  }

transport-by-iso : (C : Colimit) → NaturalIsomorphism (coapex C) X → Colimit
transport-by-iso C C≅X = transport-by-iso-cocone C (proj₂ p)
  where p = cocone-resp-iso (colimit C) C≅X
