{-# OPTIONS --without-K --safe #-}


open import Level

-- Nerves of categories

module Categories.Category.Construction.Nerve (o ℓ e : Level) where

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Fin using (Fin; fromℕ; toℕ)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (flip)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl; sym; trans)

import Function.Equality as S

open import Categories.Category using (Category; _[_,_]; _[_∘_]; _[_≈_])
open import Categories.Functor using (Functor; module Functor; _∘F_) renaming (id to idF)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ˡ_; _∘ʳ_; _∘ᵥ_) renaming (id to idNat)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _ⓘʳ_)

open import Categories.Category.Construction.Functors using (Precompose)
open import Categories.Category.Construction.KanComplex (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) using (inner; IsWeakKanComplex)
open import Categories.Category.Product using (_※_; _※ⁿ_)
open import Categories.Functor.Construction.Constant using (const; constNat)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Simplex using (Δ; ⟦_⟧; _⊚_; _≗_; face-comm; Δ-eq; Δ-monotone; Δ-pointwise; δ; ε)
open import Categories.Category.Instance.SimplicialSet using (SimplicialSet)
open import Categories.Category.Instance.SimplicialSet.Properties (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) using (ΔSet; Δ[_]; Λ[_,_]; Λ-inj; Δ-yoneda)
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
  extend : ∀ {n X Y Z} → Spine C n Y Z → C [ X , Y ] → Spine C (ℕ.suc n) X Z

record Interval (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    beginning : Category.Obj C
    ending : Category.Obj C
    path : _≅_ C beginning ending

record IntervalMorphism (C : Category o ℓ e) (tail head : Interval C) : Set (o ⊔ ℓ ⊔ e) where
  field
    beginnings : C [ Interval.beginning tail , Interval.beginning head ]
    endings : C [ Interval.ending tail , Interval.ending head ]
    paths : C [ C [ _≅_.from (Interval.path head) ∘ beginnings ] ≈ C [ endings ∘ _≅_.from (Interval.path tail) ] ]

Intervals : Category o ℓ e → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
Intervals C = record
  { Obj = Interval C
  ; _⇒_ = IntervalMorphism C
  ; _≈_ = {!   !}
  ; id = {!   !}
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }

Spine⇒Simplex₀ : ∀ (C : Category o ℓ e) n X Y → Spine C n X Y → Fin (ℕ.suc n) → Category.Obj C
Spine⇒Simplex₀ C n X Y spine Fin.zero = X
Spine⇒Simplex₀ C .(ℕ.suc _) X Y (extend spine x) (Fin.suc i) = Spine⇒Simplex₀ C _ _ Y spine i

Spine⇒Simplex₁ : ∀ (C : Category o ℓ e) n X Y (spine : Spine C n X Y) (i j : Fin (ℕ.suc n)) → toℕ i ≤ toℕ j → C [ Spine⇒Simplex₀ C n X Y spine i , Spine⇒Simplex₀ C n X Y spine j ]
Spine⇒Simplex₁ C n X Y spine Fin.zero Fin.zero i≤j = Category.id C
Spine⇒Simplex₁ C .(ℕ.suc _) X Y (extend spine f) Fin.zero (Fin.suc j) i≤j = C [ Spine⇒Simplex₁ C _ _ Y spine Fin.zero j _≤_.z≤n ∘ f ]
Spine⇒Simplex₁ C .(ℕ.suc _) X Y (extend spine _) (Fin.suc i) (Fin.suc j) (_≤_.s≤s i≤j) = Spine⇒Simplex₁ C _ _ Y spine i j i≤j

Spine⇒Simplex-identity : ∀ (C : Category o ℓ e) n X Y (spine : Spine C n X Y) (i : Fin (ℕ.suc n)) → C [ Spine⇒Simplex₁ C n X Y spine i i ≤-refl ≈ Category.id C ]
Spine⇒Simplex-identity C n X Y spine Fin.zero = Category.Equiv.refl C
Spine⇒Simplex-identity C .(ℕ.suc _) X Y (extend spine _) (Fin.suc i) = Spine⇒Simplex-identity C _ _ Y spine i

Spine⇒Simplex-homomorphism : ∀ (C : Category o ℓ e) n X Y (spine : Spine C n X Y) (i j k : Fin (ℕ.suc n)) (i≤j : toℕ i ≤ toℕ j) (j≤k : toℕ j ≤ toℕ k) → C [ Spine⇒Simplex₁ C n X Y spine i k (≤-trans i≤j j≤k) ≈ C [ Spine⇒Simplex₁ C n X Y spine j k j≤k ∘ Spine⇒Simplex₁ C n X Y spine i j i≤j ] ]
Spine⇒Simplex-homomorphism C n X Y spine Fin.zero Fin.zero k _≤_.z≤n _≤_.z≤n = Category.Equiv.sym C (Category.identityʳ C)
Spine⇒Simplex-homomorphism C .(ℕ.suc _) X Y (extend spine f) Fin.zero (Fin.suc j) (Fin.suc k) _≤_.z≤n (_≤_.s≤s j≤k) = let open Category.HomReasoning C in
  begin
    C [ Spine⇒Simplex₁ C _ _ Y spine Fin.zero k _≤_.z≤n ∘ f ]
  ≈⟨ Category.∘-resp-≈ˡ C (Spine⇒Simplex-homomorphism C _ _ Y spine Fin.zero j k _≤_.z≤n j≤k) ⟩
    C [ C [ Spine⇒Simplex₁ C _ _ Y spine j k j≤k ∘ Spine⇒Simplex₁ C _ _ Y spine Fin.zero j _≤_.z≤n ] ∘ f ]
  ≈⟨ Category.assoc C ⟩
    C [ Spine⇒Simplex₁ C _ _ Y spine j k j≤k ∘ C [ Spine⇒Simplex₁ C _ _ Y spine Fin.zero j _≤_.z≤n ∘ f ] ]
  ∎
Spine⇒Simplex-homomorphism C .(ℕ.suc _) X Y (extend spine _) (Fin.suc i) (Fin.suc j) (Fin.suc k) (_≤_.s≤s i≤j) (_≤_.s≤s j≤k) = Spine⇒Simplex-homomorphism C _ _ Y spine i j k i≤j j≤k

Spine⇒Simplex-resp-≈ : ∀ (C : Category o ℓ e) n X Y (spine : Spine C n X Y) (i j : Fin (ℕ.suc n)) (pf₁ pf₂ : toℕ i ≤ toℕ j) → C [ Spine⇒Simplex₁ C n X Y spine i j pf₁ ≈ Spine⇒Simplex₁ C n X Y spine i j pf₂ ]
Spine⇒Simplex-resp-≈ C n X Y spine Fin.zero Fin.zero pf₁ pf₂ = Category.Equiv.refl C
Spine⇒Simplex-resp-≈ C n X Y (extend spine f) Fin.zero (Fin.suc j) pf₁ pf₂ = Category.Equiv.refl C
Spine⇒Simplex-resp-≈ C .(ℕ.suc _) X Y (extend spine _) (Fin.suc i) (Fin.suc j) (_≤_.s≤s pf₁) (_≤_.s≤s pf₂) = Spine⇒Simplex-resp-≈ C _ _ Y spine i j pf₁ pf₂

Spine⇒Simplex : ∀ (C : Category o ℓ e) n X Y → Spine C n X Y → Functor (CategorialSimplex (ℕ.suc n)) C
Spine⇒Simplex C n X Y spine = record
  { F₀ = Spine⇒Simplex₀ C n X Y spine
  ; F₁ = λ {i j} → Spine⇒Simplex₁ C n X Y spine i j
  ; identity = λ {i} → Spine⇒Simplex-identity C n X Y spine i
  ; homomorphism = λ {i} {j} {k} {i≤j} {j≤k} → Spine⇒Simplex-homomorphism C n X Y spine i j k i≤j j≤k
  ; F-resp-≈ = λ {i j pf₁ pf₂} _ → Spine⇒Simplex-resp-≈ C n X Y spine i j pf₁ pf₂
  }

Nerve : Functor (Cats o ℓ e) (SimplicialSet _ _)
Nerve = Functor.F₀ Precompose (Functor.op S-on-Δ) ∘F (Yoneda.Yoneda.embed (Cats o ℓ e))

facetSimplex : ∀ (X : ΔSet) {n} (simplex : Δ[ n ] ⇒ X) {m} → Δ [ m , n ] → Δ[ m ] ⇒ X
facetSimplex X {n} simplex {m} map = (simplex ∘ᵥ _∘ˡ_ {G = idF ※ const m} {idF ※ const n} (LiftSetoids _ _ ∘F Hom[ Δ ][-,-]) (idNat ※ⁿ constNat map))

facetSimplex-congm : ∀ (X : ΔSet) {n} (simplex : Δ[ n ] ⇒ X) {m} (f g : Δ [ m , n ]) → f ≗ g → facetSimplex X simplex f ≈ facetSimplex X simplex g
facetSimplex-congm X {n} simplex {m} f g f≗g {k} {x} {y} x≗y = S.cong (NaturalTransformation.η simplex k) (lift (Δ-eq (trans (cong ⟦ f ⟧ (Δ-pointwise (lower x≗y))) (Δ-pointwise f≗g))))

facetSimplex-congs : ∀ (X : ΔSet) {n} (simplex₁ simplex₂ : Δ[ n ] ⇒ X) (simplex₁₌₂ : simplex₁ ≈ simplex₂) {m} (f : Δ [ m , n ]) → facetSimplex X simplex₁ f ≈ facetSimplex X simplex₂ f
facetSimplex-congs X {n} simplex₁ simplex₂ simplex₁₌₂ {m} f {k} {x} {y} x≗y = simplex₁₌₂ {k} {lift (f ⊚ lower x ⊚ ε)} {lift (f ⊚ lower y ⊚ ε)} (lift (Δ-eq (cong ⟦ f ⟧ (Δ-pointwise (lower x≗y)))))

facetSimplex-hmm : ∀ (X : ΔSet) {n} (simplex : Δ[ n ] ⇒ X) {m p} (g : Δ [ m , n ]) (f : Δ [ p , m ]) → facetSimplex X (facetSimplex X simplex g) f ≈ facetSimplex X simplex (g ⊚ f)
facetSimplex-hmm X {n} simplex {m} {p} g f {k} {x} {y} x≗y = S.cong (NaturalTransformation.η simplex k) (lift (Δ-eq (cong ⟦ g ⟧ (cong ⟦ f ⟧ (Δ-pointwise (lower x≗y))))))

Horn-face : ∀ n-1 k j → j ≢ inner k → (Δ[ n-1 ] ⇒ Λ[ ℕ.suc n-1 , inner k ])
Horn-face (ℕ.suc n-2) k j j≢k = record
  { η = λ m → record
    { _⟨$⟩_ = λ m⇒n → lift record
      { horn = record { hom = Δ [ δ j ∘ lower m⇒n ] ; factor = lower m⇒n ; factor-dim = j ; factor-face = Δ-eq refl }
      ; is-horn = j≢k
      }
    ; cong = λ {m⇒n₁} {m⇒n₂} m⇒n₁₌₂ → lift (Δ-eq (cong ⟦ δ j ⟧ (Δ-pointwise (lower m⇒n₁₌₂))))
    }
  ; commute = λ {m p} p⇒m {m⇒n₁ m⇒n₂} m⇒n₁₌₂ → lift (Δ-eq (cong ⟦ δ j ⟧ (Δ-pointwise (lower m⇒n₁₌₂))))
  ; sym-commute = λ {m p} p⇒m {m⇒n₁ m⇒n₂} m⇒n₁₌₂ → lift (Δ-eq (cong ⟦ δ j ⟧ (Δ-pointwise (lower m⇒n₁₌₂)))) }

Horn-face-cong : ∀ X n-1 k j₁ j₂ (j₁≢k : j₁ ≢ inner k) (j₂≢k : j₂ ≢ inner k) m (ϕ₁ ϕ₂ : Δ [ m , n-1 ]) (horn : Λ[ ℕ.suc n-1 , inner k ] ⇒ X) → Δ [ δ j₁ ⊚ ϕ₁ ≈ δ j₂ ⊚ ϕ₂ ] → facetSimplex X (horn ∘ᵥ Horn-face n-1 k j₁ j₁≢k) ϕ₁ ≈ facetSimplex X (horn ∘ᵥ Horn-face n-1 k j₂ j₂≢k) ϕ₂
Horn-face-cong X (ℕ.suc n-2) k j₁ j₂ j₁≢k j₂≢k m ϕ₁ ϕ₂ horn comm {p} {x₁} {x₂} x₁₌₂ = S.cong (NaturalTransformation.η horn p) (lift (Δ-eq (trans (cong ⟦ δ j₁ ⊚ ϕ₁ ⟧ (Δ-pointwise (lower x₁₌₂))) (Δ-pointwise comm))))

realpred : ∀ {n-2} → Fin (ℕ.suc (ℕ.suc n-2)) → Fin (ℕ.suc n-2)
realpred Fin.zero = Fin.zero
realpred (Fin.suc k-1) = k-1

Horn-last-face-lemma : ∀ n-1 k → fromℕ (ℕ.suc n-1) ≢ inner k
Horn-last-face-lemma .(ℕ.suc _) Fin.zero ()
Horn-last-face-lemma .(ℕ.suc _) (Fin.suc k-1) n≡k = Horn-last-face-lemma _ k-1 (cong realpred n≡k)

Horn-last-face : ∀ n-1 k → (Δ[ n-1 ] ⇒ Λ[ ℕ.suc n-1 , inner k ])
Horn-last-face n-1 k = Horn-face n-1 k (fromℕ (ℕ.suc n-1)) (Horn-last-face-lemma n-1 k)

Horn-first-face : ∀ n-1 k → (Δ[ n-1 ] ⇒ Λ[ ℕ.suc n-1 , inner k ])
Horn-first-face n-1 k = Horn-face n-1 k Fin.zero λ ()

Simplex-start : ∀ (C : Category o ℓ e) {n} (simplex : Δ[ n ] ⇒ Functor.F₀ Nerve C) → Category.Obj C
Simplex-start C {ℕ.zero} simplex = Functor.F₀ (NaturalTransformation.η simplex 0 S.⟨$⟩ lift ε) (lift Fin.zero)
Simplex-start C {ℕ.suc n} simplex = Simplex-start C {n} (facetSimplex _ simplex (δ (fromℕ (ℕ.suc n))))

Simplex-end : ∀ (C : Category o ℓ e) {n} (simplex : Δ[ n ] ⇒ Functor.F₀ Nerve C) → Category.Obj C
Simplex-end C {ℕ.zero} simplex = Functor.F₀ (NaturalTransformation.η simplex 0 S.⟨$⟩ lift ε) (lift Fin.zero)
Simplex-end C {ℕ.suc n} simplex = Simplex-end C {n} (facetSimplex _ simplex (δ Fin.zero))

Simplex-start-coh : ∀ (C : Category o ℓ e) {n} (simplex₁ simplex₂ : Δ[ n ] ⇒ Functor.F₀ Nerve C) → simplex₁ ≈ simplex₂ → C [ Simplex-start C {n} simplex₁ , Simplex-start C {n} simplex₂ ]
Simplex-start-coh C {ℕ.zero} simplex₁ simplex₂ simplex₁₌₂ = NaturalTransformation.η (NaturalIsomorphism.F⇒G (simplex₁₌₂ {0} {lift ε} {lift ε} (lift (Δ-eq refl)))) (lift Fin.zero)
Simplex-start-coh C {ℕ.suc n} simplex₁ simplex₂ simplex₁₌₂ = Simplex-start-coh C {n}
  (facetSimplex _ simplex₁ (δ (fromℕ (ℕ.suc n))))
  (facetSimplex _ simplex₂ (δ (fromℕ (ℕ.suc n))))
  (facetSimplex-congs _ simplex₁ simplex₂ simplex₁₌₂ (δ (fromℕ (ℕ.suc n))))

Simplex-shoulder-coh : ∀ (C : Category o ℓ e) n-2 (simplex : Δ[ ℕ.suc (ℕ.suc n-2) ] ⇒ Functor.F₀ Nerve C) → C [ Simplex-start C (facetSimplex _ (facetSimplex _ simplex (δ (fromℕ (ℕ.suc (ℕ.suc n-2))))) (δ Fin.zero)) , Simplex-start C (facetSimplex _ simplex (δ Fin.zero)) ]
Simplex-shoulder-coh C n-2 simplex =
  let N = Functor.F₀ Nerve C
      n-1 = ℕ.suc n-2
      n = ℕ.suc n-1
      open HomReasoning
  in Simplex-start-coh C (facetSimplex N {n-1} (facetSimplex N {n} simplex (δ (fromℕ n))) (δ Fin.zero)) (facetSimplex N {n-1} (facetSimplex N {n} simplex (δ Fin.zero)) (δ (fromℕ n-1))) (
        begin
          facetSimplex N {n-1} (facetSimplex N {n} simplex (δ (fromℕ n))) (δ Fin.zero)
        ≈⟨ facetSimplex-hmm N simplex (δ (fromℕ n)) (δ Fin.zero) ⟩
          facetSimplex N {n} simplex (δ (fromℕ n) ⊚ δ Fin.zero)
        ≈⟨ facetSimplex-congm N {n} simplex (δ (fromℕ n) ⊚ δ Fin.zero) (δ Fin.zero ⊚ δ (fromℕ n-1)) (Category.Equiv.sym Δ (face-comm Fin.zero (Fin.suc (fromℕ n-2)) _≤_.z≤n)) ⟩
          facetSimplex N {n} simplex (δ Fin.zero ⊚ δ (fromℕ n-1))
        ≈⟨ Equiv.sym {Δ[ n-2 ]} {N} {facetSimplex N (facetSimplex N simplex (δ Fin.zero)) (δ (Fin.suc (fromℕ n-2)))} {facetSimplex N simplex (δ Fin.zero ⊚ δ (Fin.suc (fromℕ n-2)))} (facetSimplex-hmm N simplex (δ Fin.zero) (δ (fromℕ n-1))) ⟩
          facetSimplex N {n-1} (facetSimplex N {n} simplex (δ Fin.zero)) (δ (fromℕ n-1))
        ∎)

Simplex-neck : ∀ (C : Category o ℓ e) {n-1} (simplex : Δ[ ℕ.suc n-1 ] ⇒ Functor.F₀ Nerve C) → C [ Simplex-start C simplex , Simplex-start C (facetSimplex _ simplex (δ Fin.zero)) ]
Simplex-neck C {ℕ.zero} simplex =
  let module NT = NaturalTransformation
      module NI = NaturalIsomorphism
      module C = Category C
  in NT.η (NI.F⇒G (S.cong (NT.η simplex 0) {lift (ε ⊚ ε ⊚ δ Fin.zero)} {lift (δ Fin.zero ⊚ ε ⊚ ε)} (lift (Δ-eq refl)))) (lift Fin.zero)
     C.∘ NT.η (NI.F⇒G (NT.sym-commute simplex (δ Fin.zero) {lift ε} {lift ε} (lift (Δ-eq refl)))) (lift Fin.zero)
     C.∘ Functor.F₁ (NT.η simplex 1 S.⟨$⟩ lift ε) (lift (_≤_.z≤n {1}))
     C.∘ (NT.η (NI.F⇒G (NT.commute simplex (δ (Fin.suc Fin.zero)) {lift ε} {lift ε} (lift (Δ-eq refl)))) (lift Fin.zero)
     C.∘ NT.η (NI.F⇒G (S.cong (NT.η simplex 0) {lift (δ (Fin.suc Fin.zero) ⊚ ε ⊚ ε)} {lift (ε ⊚ ε ⊚ δ (Fin.suc Fin.zero))} (lift (Δ-eq refl)))) (lift Fin.zero))
Simplex-neck C {ℕ.suc n-1} simplex =
  let module NT = NaturalTransformation
      module NI = NaturalIsomorphism
      module C = Category C
  in Simplex-shoulder-coh C n-1 simplex
     C.∘ Simplex-neck C {n-1} (facetSimplex _ simplex (δ (fromℕ (ℕ.suc (ℕ.suc n-1)))))

Simplex⇒Spine : ∀ (C : Category o ℓ e) {n} (simplex : Δ[ n ] ⇒ Functor.F₀ Nerve C) → Spine C n (Simplex-start C simplex) (Simplex-end C simplex)
Simplex⇒Spine C {ℕ.zero} simplex = start (Simplex-start C simplex)
Simplex⇒Spine C {ℕ.suc n} simplex = extend (Simplex⇒Spine C (facetSimplex _ simplex (δ Fin.zero))) (Simplex-neck C simplex)

Horn-start : ∀ (C : Category o ℓ e) {n-1} {k} → Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C → Category.Obj C
Horn-start C {ℕ.suc n-2} {k} horn = Simplex-start C (horn ∘ᵥ Horn-last-face (ℕ.suc n-2) k)

Horn-end : ∀ (C : Category o ℓ e) {n-1} {k} → Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C → Category.Obj C
Horn-end C {ℕ.suc n-2} {k} horn = Simplex-end C (horn ∘ᵥ Horn-first-face (ℕ.suc n-2) k)

Horn-neck : ∀ (C : Category o ℓ e) n-2 k (horn : Λ[ ℕ.suc (ℕ.suc n-2) , inner k ] ⇒ Functor.F₀ Nerve C) → C [ Simplex-start C (horn ∘ᵥ Horn-last-face (ℕ.suc n-2) k) , Simplex-start C (horn ∘ᵥ Horn-first-face (ℕ.suc n-2) k) ]
Horn-neck C n-2 k horn =
  let module C = Category C
      N = Functor.F₀ Nerve C
      n-1 = ℕ.suc n-2
      n = ℕ.suc n-1
  in Simplex-start-coh C
       (facetSimplex N {n-1} (horn ∘ᵥ Horn-last-face n-1 k) (δ Fin.zero))
       (facetSimplex N {n-1} (horn ∘ᵥ Horn-first-face n-1 k) (δ (fromℕ n-1)))
       (Horn-face-cong N n-1 k (fromℕ n) Fin.zero (Horn-last-face-lemma n-1 k) (λ ()) n-2 (δ Fin.zero) (δ (fromℕ n-1)) horn (Category.Equiv.sym Δ (face-comm Fin.zero (fromℕ n-1) _≤_.z≤n)))
     C.∘ Simplex-neck C (horn ∘ᵥ Horn-last-face (ℕ.suc n-2) k)

Horn⇒Spine : ∀ (C : Category o ℓ e) {n-1} {k} (horn : Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C) → Spine C (ℕ.suc n-1) (Horn-start C horn) (Horn-end C horn)
Horn⇒Spine C {ℕ.suc n-2} {k} horn = extend (Simplex⇒Spine C (horn ∘ᵥ Horn-first-face (ℕ.suc n-2) k)) (Horn-neck C n-2 k horn)

Nerve-filler : ∀ (C : Category o ℓ e) {n-1} {k} → Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C → Setoid.Carrier (Functor.F₀ (Functor.F₀ Nerve C) (ℕ.suc n-1))
Nerve-filler C {n-1} {k} horn = Spine⇒Simplex C _ _ _ (Horn⇒Spine C horn) ∘F unliftF o ℓ e (CategorialSimplex (ℕ.suc (ℕ.suc n-1)))

Nerve-filler-cong : ∀ (C : Category o ℓ e) {n-1} {k} (horn₁ horn₂ : Λ[ ℕ.suc n-1 , inner k ] ⇒ Functor.F₀ Nerve C) → horn₁ ≈ horn₂ → NaturalIsomorphism (Nerve-filler C horn₁) (Nerve-filler C horn₂)
Nerve-filler-cong C {n-1} {k} horn₁ horn₂ horn₁₌₂ = {!   !} ⓘʳ unliftF o ℓ e (CategorialSimplex (ℕ.suc (ℕ.suc n-1)))

Category⇒Nerve : (C : Category o ℓ e) -> Σ ΔSet IsNerve
Category⇒Nerve C = Functor.F₀ Nerve C , record
  { isWeakKanComplex = record
    { filler = λ {n-1 k} horn → Δ-yoneda (Functor.F₀ Nerve C) (ℕ.suc n-1) S.⟨$⟩ Nerve-filler C horn
    ; filler-cong = λ {n-1 k} {horn₁ horn₂} horn₁₌₂ → S.cong (Δ-yoneda (Functor.F₀ Nerve C) (ℕ.suc n-1)) (Nerve-filler-cong C horn₁ horn₂ horn₁₌₂)
    ; is-filler = {!   !}
    }
  ; filler-unique = {!   !} }