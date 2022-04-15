{-# OPTIONS --without-K --safe #-}
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (module Setoid)
open import Function.Equality using (_⟶_; _⟨$⟩_)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₂)
open import Categories.Functor.Profunctor hiding (id)
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Category.Instance.Setoids

-- Cocone over a Functor F (from shape category J into category C) with weight W

module Categories.Diagram.Cocone.General
  {o ℓ e} {o′ ℓ′ e′} {o″ ℓ″ e″} {ℓ‴ e‴} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} {K : Category o″ ℓ″ e″} (W : Profunctor ℓ‴ e‴ K J) (F : Functor J C) where

open import Categories.Morphism.Reasoning C

private
  module W = Profunctor W
open Category C
open HomReasoning
open Functor F

open import Level

record Coapex (N : Functor K C) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″ ⊔ ℓ‴ ⊔ e‴) where
  private module N = Functor N
  field
    ψ       : (k : Category.Obj K) (j : Category.Obj J) → W.₀ (j , k) ⟶ hom-setoid {F₀ j} {N.₀ k}
    commute : ∀ {A B} (g : K [ A , B ]) {X Y} (f : J [ X , Y ]) (w : Setoid.Carrier (W.₀ (Y , A))) → N.₁ g ∘ (ψ A Y ⟨$⟩ w) ∘ F₁ f ≈ ψ B X ⟨$⟩ (W.₁ (f , g) ⟨$⟩ w)

record Cocone : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″ ⊔ ℓ‴ ⊔ e‴) where
  field
    {N}    : Functor K C
    coapex : Coapex N

  open Coapex coapex public

open Cocone using (N; ψ)

record Cocone⇒ (c c′ : Cocone) : Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″ ⊔ ℓ‴) where
  field
    arr     : NaturalTransformation (N c) (N c′)
    commute : ∀ {A} {X} {w} → NaturalTransformation.η arr A ∘ (ψ c A X ⟨$⟩ w) ≈ ψ c′ A X ⟨$⟩ w

Cocone-as-extension : Cocone → Functor W.cograph C
Cocone-as-extension κ = record
  { F₀ = λ
    { (inj₁ x) → F₀ x
    ; (inj₂ y) → Functor.F₀ κ.N y
    }
  ; F₁ = λ
    { {inj₁ x} {inj₁ y} f → F₁ (lower f)
    ; {inj₁ x} {inj₂ y} f → κ.ψ y x ⟨$⟩ f
    ; {inj₂ x} {inj₂ y} f → Functor.F₁ κ.N (lower f)
    }
  ; identity = λ
    { {inj₁ x} → identity
    ; {inj₂ y} → Functor.identity κ.N
    }
  ; homomorphism = λ
    { {inj₁ x} {inj₁ y} {inj₁ z} {f} {g} → homomorphism
    ; {inj₁ x} {inj₁ y} {inj₂ z} {f} {g} →
      begin
        κ.ψ z x ⟨$⟩ (W.F₁ (lower f , Category.id K) ⟨$⟩ g)
      ≈˘⟨ κ.commute (Category.id K) (lower f) g ⟩
        Functor.F₁ κ.N (Category.id K) ∘ (κ.ψ z y ⟨$⟩ g) ∘ F₁ (lower f)
      ≈⟨ Functor.identity κ.N ⟩∘⟨refl ⟩
        id ∘ (κ.ψ z y ⟨$⟩ g) ∘ F₁ (lower f)
      ≈⟨ identityˡ ⟩
        (κ.ψ z y ⟨$⟩ g) ∘ F₁ (lower f)
      ∎
    ; {inj₁ x} {inj₂ y} {inj₂ z} {f} {g} →
      begin
        κ.ψ z x ⟨$⟩ (W.F₁ (Category.id J , lower g) ⟨$⟩ f)
      ≈˘⟨ κ.commute (lower g) (Category.id J) f ⟩
        Functor.F₁ κ.N (lower g) ∘ (κ.ψ y x ⟨$⟩ f) ∘ F₁ (Category.id J)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identity ⟩
        Functor.F₁ κ.N (lower g) ∘ (κ.ψ y x ⟨$⟩ f) ∘ id
      ≈⟨ refl⟩∘⟨ identityʳ ⟩
        Functor.F₁ κ.N (lower g) ∘ (κ.ψ y x ⟨$⟩ f)
      ∎
    ; {inj₂ x} {inj₂ y} {inj₂ z} {f} {g} → Functor.homomorphism κ.N
    }
  ; F-resp-≈ = λ
    { {inj₁ x} {inj₁ y} {f} {g} f≈g → F-resp-≈ (lower f≈g)
    ; {inj₁ x} {inj₂ y} {f} {g} f≈g → Function.Equality.cong (κ.ψ y x) f≈g
    ; {inj₂ x} {inj₂ y} {f} {g} f≈g → Functor.resp-≈ κ.N (lower f≈g)
    }
  }
  where module κ = Cocone κ

-- it's the identity, just need to expand enough for it to compute
Cocone-as-extension-extends : ∀ κ → NaturalIsomorphism (Cocone-as-extension κ ∘F W.cograph.Inj₁) F
Cocone-as-extension-extends κ = record
  { F⇒G = record
    { η = NaturalTransformation.η {F = F} idN
    ; commute = NaturalTransformation.commute {F = F} idN
    ; sym-commute = NaturalTransformation.sym-commute {F = F} idN
    }
  ; F⇐G = record
    { η = NaturalTransformation.η {F = F} idN
    ; commute = NaturalTransformation.commute {F = F} idN
    ; sym-commute = NaturalTransformation.sym-commute {F = F} idN }
  ; iso = λ X → record
    { isoˡ = identity²
    ; isoʳ = identity²
    }
  }
  where module κ = Cocone κ

extension-as-Cocone : ∀ G → NaturalIsomorphism (G ∘F W.cograph.Inj₁) F → Cocone
extension-as-Cocone G pin = record
  { N = G ∘F W.cograph.Inj₂
  ; coapex = record
    { ψ = λ k j → record
      { _⟨$⟩_ = λ f → G.₁ f ∘ pin.⇐.η j
      ; cong = λ eq → ∘-resp-≈ˡ (G.resp-≈ eq)
      }
    ; commute = λ {A B} g {X Y} f w →
      begin
        G.F₁ (lift g) ∘ (G.F₁ w ∘ pin.⇐.η Y) ∘ F₁ f
      ≈⟨ pushʳ (extendˡ (pin.⇐.commute f)) ⟩
        (G.F₁ (lift g) ∘ G.F₁ w ∘ G.F₁ (lift f)) ∘ pin.⇐.η X
      ≈˘⟨ ∘-resp-≈ʳ (Functor.homomorphism G) ⟩∘⟨refl ⟩
        (G.F₁ (lift g) ∘ G.F₁ (W.F₁ (f , Category.id K) ⟨$⟩ w)) ∘ pin.⇐.η X
      ≈˘⟨ Functor.homomorphism G ⟩∘⟨refl ⟩
        G.F₁ (W.F₁ (Category.id J , g) ⟨$⟩ (W.F₁ (f , Category.id K) ⟨$⟩ w)) ∘ pin.⇐.η X
      ≈˘⟨ G.resp-≈ ([ W.bimodule ]-decompose₂ (Setoid.refl (W.F₀ (Y , A)))) ⟩∘⟨refl ⟩
        G.F₁ (W.F₁ (f , g) ⟨$⟩ w) ∘ pin.⇐.η X
      ∎
    }
  }
  where
  module G = Functor G
  module pin = NaturalIsomorphism pin

record CoconeEx : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″ ⊔ e″ ⊔ ℓ‴ ⊔ e‴) where
  field
    extension : Functor W.cograph C
    pin : NaturalIsomorphism (extension ∘F W.cograph.Inj₁) F

  module extension = Functor extension
  module pin = NaturalIsomorphism pin

Cocone-as-CoconeEx : Cocone → CoconeEx
Cocone-as-CoconeEx κ = record { extension = Cocone-as-extension κ ; pin = Cocone-as-extension-extends κ }

CoconeEx-as-Cocone : CoconeEx → Cocone
CoconeEx-as-Cocone x = extension-as-Cocone x.extension x.pin
  where module x = CoconeEx x

record CoconeEx⇒ (x y : CoconeEx): Set (ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ o″ ⊔ ℓ″ ⊔ ℓ‴) where
  private
    module x = CoconeEx x
    module y = CoconeEx y
  field
    arr : NaturalTransformation x.extension y.extension
    commute : y.pin.F⇒G ∘ᵥ (arr ∘ʳ W.cograph.Inj₁) ≃ x.pin.F⇒G

  module arr = NaturalTransformation arr

  commute-other : (arr ∘ʳ W.cograph.Inj₁) ∘ᵥ x.pin.F⇐G ≃ y.pin.F⇐G
  commute-other {j} =
    begin
      arr.η (inj₁ j) ∘ x.pin.⇐.η j
    ≈⟨ insertˡ (y.pin.iso.isoˡ j) ⟩
      y.pin.⇐.η j ∘ y.pin.⇒.η j ∘ arr.η (inj₁ j) ∘ x.pin.⇐.η j
    ≈⟨ refl⟩∘⟨ pullˡ commute ⟩
      y.pin.⇐.η j ∘ x.pin.⇒.η j ∘ x.pin.⇐.η j
    ≈⟨ elimʳ (x.pin.iso.isoʳ j) ⟩
      y.pin.⇐.η j
    ∎

Cocone⇒-as-CoconeEx⇒ : ∀ {κ κ′} → Cocone⇒ κ κ′ → CoconeEx⇒ (Cocone-as-CoconeEx κ) (Cocone-as-CoconeEx κ′)
Cocone⇒-as-CoconeEx⇒ f = record
  { arr = record
    { η = λ { (inj₁ x) → id ; (inj₂ y) → NaturalTransformation.η f.arr y }
    ; commute = λ
      { {inj₁ x} {inj₁ y} g → NaturalTransformation.commute {F = F} idN (lower g)
      ; {inj₁ x} {inj₂ y} g → Equiv.trans f.commute (Equiv.sym identityʳ)
      ; {inj₂ x} {inj₂ y} g → NaturalTransformation.commute f.arr (lower g)
      }
    ; sym-commute = λ
      { {inj₁ x} {inj₁ y} g → NaturalTransformation.sym-commute {F = F} idN (lower g)
      ; {inj₁ x} {inj₂ y} g → Equiv.trans identityʳ (Equiv.sym f.commute)
      ; {inj₂ x} {inj₂ y} g → NaturalTransformation.sym-commute f.arr (lower g)
      }
    }
  ; commute = identity²
  }
  where module f = Cocone⇒ f

Cocone⇒-as-CoconeEx⇒′ : ∀ {κ κ′} → Cocone⇒ κ (CoconeEx-as-Cocone κ′) → CoconeEx⇒ (Cocone-as-CoconeEx κ) κ′
Cocone⇒-as-CoconeEx⇒′ {κ} {κ′} f = record
  { arr = record
    { η = λ { (inj₁ x) → κ′.pin.⇐.η x ; (inj₂ y) → NaturalTransformation.η f.arr y }
    ; commute = λ
      { {inj₁ x} {inj₁ y} g → NaturalTransformation.commute κ′.pin.F⇐G (lower g)
      ; {inj₁ x} {inj₂ y} g → f.commute
      ; {inj₂ x} {inj₂ y} g → NaturalTransformation.commute f.arr (lower g)
      }
    ; sym-commute = λ
      { {inj₁ x} {inj₁ y} g → NaturalTransformation.sym-commute κ′.pin.F⇐G (lower g)
      ; {inj₁ x} {inj₂ y} g → Equiv.sym f.commute
      ; {inj₂ x} {inj₂ y} g → NaturalTransformation.sym-commute f.arr (lower g)
      }
    }
  ; commute = κ′.pin.iso.isoʳ _
  }
  where
  module f = Cocone⇒ f
  module κ′ = CoconeEx κ′

Cocone⇒-as-CoconeEx⇒″ : ∀ {x κ} → Cocone⇒ (CoconeEx-as-Cocone x) κ → CoconeEx⇒ x (Cocone-as-CoconeEx κ)
Cocone⇒-as-CoconeEx⇒″ {x} f = record
  { arr = record
    { η = λ { (inj₁ j) → x.pin.⇒.η j ; (inj₂ k) → NaturalTransformation.η f.arr k }
    ; commute = λ
      { {inj₁ a} {inj₁ b} g → NaturalTransformation.commute x.pin.F⇒G (lower g)
      ; {inj₁ a} {inj₂ b} g → switch-tofromʳ x.pin.FX≅GX (Equiv.trans assoc f.commute)
      ; {inj₂ a} {inj₂ b} g → NaturalTransformation.commute f.arr (lower g)
      }
    ; sym-commute = λ
      { {inj₁ a} {inj₁ b} g → NaturalTransformation.sym-commute x.pin.F⇒G (lower g)
      ; {inj₁ a} {inj₂ b} g → Equiv.sym (switch-tofromʳ x.pin.FX≅GX (Equiv.trans assoc f.commute))
      ; {inj₂ a} {inj₂ b} g → NaturalTransformation.sym-commute f.arr (lower g)
      }
    }
  ; commute = identityˡ
  }
  where
  module f = Cocone⇒ f
  module x = CoconeEx x

CoconeEx⇒-as-Cocone⇒ : ∀ {x y} → CoconeEx⇒ x y → Cocone⇒ (CoconeEx-as-Cocone x) (CoconeEx-as-Cocone y)
CoconeEx⇒-as-Cocone⇒ {x} {y} f = record
  { arr = f.arr ∘ʳ W.cograph.Inj₂
  ; commute = λ {k j w} →
    begin
      f.arr.η (inj₂ k) ∘ x.extension.F₁ w ∘ x.pin.⇐.η j
    ≈⟨ extendʳ (f.arr.commute w) ⟩
      y.extension.F₁ w ∘ f.arr.η (inj₁ j) ∘ x.pin.⇐.η j
    ≈⟨ refl⟩∘⟨ f.commute-other ⟩
      y.extension.F₁ w ∘ y.pin.⇐.η j
    ∎
  }
  where
  module x = CoconeEx x
  module y = CoconeEx y
  module f = CoconeEx⇒ f

CoconeEx⇒-as-Cocone⇒′ : ∀ {x κ} → CoconeEx⇒ x (Cocone-as-CoconeEx κ) → Cocone⇒ (CoconeEx-as-Cocone x) κ
CoconeEx⇒-as-Cocone⇒′ {x} {κ} f = record
  { arr = record
    { η = λ k → f.arr.η (inj₂ k)
    ; commute = λ g → f.arr.commute (lift g)
    ; sym-commute = λ g → f.arr.sym-commute (lift g)
    }
  ; commute = λ {k j w} →
    begin
      f.arr.η (inj₂ k) ∘ x.extension.F₁ w ∘ x.pin.⇐.η j
    ≈⟨ extendʳ (f.arr.commute w) ⟩
      (κ.ψ k j ⟨$⟩ w) ∘ f.arr.η (inj₁ j) ∘ x.pin.⇐.η j
    ≈⟨ elimʳ f.commute-other ⟩
      κ.ψ k j ⟨$⟩ w
    ∎
  }
  where
  module x = CoconeEx x
  module κ = Cocone κ
  module f = CoconeEx⇒ f

CoconeEx⇒-as-Cocone⇒″ : ∀ {κ y} → CoconeEx⇒ (Cocone-as-CoconeEx κ) y → Cocone⇒ κ (CoconeEx-as-Cocone y)
CoconeEx⇒-as-Cocone⇒″ {κ} {y} f = record
  { arr = record
    { η = λ k → f.arr.η (inj₂ k)
    ; commute = λ g → f.arr.commute (lift g)
    ; sym-commute = λ g → f.arr.sym-commute (lift g)
    }
  ; commute = λ {k j w} →
    begin
      f.arr.η (inj₂ k) ∘ (κ.ψ k j ⟨$⟩ w)
    ≈⟨ f.arr.commute w ⟩
      y.extension.F₁ w ∘ f.arr.η (inj₁ j)
    ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
      y.extension.F₁ w ∘ f.arr.η (inj₁ j) ∘ id
    ≈⟨ refl⟩∘⟨ f.commute-other ⟩
      y.extension.F₁ w ∘ y.pin.⇐.η j
    ∎
  }
  where
  module κ = Cocone κ
  module y = CoconeEx y
  module f = CoconeEx⇒ f
