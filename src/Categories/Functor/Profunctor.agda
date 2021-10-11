{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Profunctor where

open import Level
open import Data.Product using (_,_; _×_)
open import Function using () renaming (_∘′_ to _∙_)
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary using (Setoid; module Setoid)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category
open import Categories.Category.Construction.Functors using (Functors; curry)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Product using ()
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)
open import Categories.Functor.Bifunctor.Properties using ([_]-commute)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Morphism.Reasoning using (id-comm; id-comm-sym)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open Setoid renaming (_≈_ to _[[_≈_]])

record Profunctor {o ℓ e} {o′ ℓ′ e′} ℓ″ e″ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ o′ ⊔ suc (ℓ ⊔ ℓ′ ⊔ ℓ″ ⊔ e ⊔ e′ ⊔ e″)) where
  constructor pro
  field
    bimodule : Bifunctor (Category.op D) C (Setoids (ℓ ⊔ ℓ′ ⊔ ℓ″) (e ⊔ e′ ⊔ e″))
  open Bifunctor bimodule public

id : ∀ {o ℓ e} → {C : Category o ℓ e} → Profunctor zero zero C C
id {C = C} = pro (Hom[ C ][-,-])

module FormalComposite {o ℓ e} {ℓ′ e′ ℓ″ e″} (C : Category o ℓ e) (F : Functor C (Setoids ℓ′ e′)) (G : Functor (Category.op C) (Setoids ℓ″ e″)) where
  open Category C
  open Functor F
  module G = Functor G

  record T : Set (o ⊔ ℓ′ ⊔ ℓ″) where
    field
      rendezvous : Obj
      in-side : Setoid.Carrier (F₀ rendezvous)
      out-side : Setoid.Carrier (G.₀ rendezvous)

  record Twines (A B : T) : Set (ℓ ⊔ e′ ⊔ e″) where
    field
      twiner : C [ T.rendezvous A , T.rendezvous B ]
      in-tertwines : F₀ (T.rendezvous B) [[ T.in-side B ≈ F₁ twiner ⟨$⟩ (T.in-side A) ]]
      out-ertwines : G.₀ (T.rendezvous A) [[ T.out-side A ≈ G.₁ twiner ⟨$⟩ (T.out-side B) ]]

  open Twines

  category : Category _ _ _
  category = record
    { Obj = T
    ; _⇒_ = Twines
    ; _≈_ = λ f g → C [ Twines.twiner f ≈ Twines.twiner g ]
    ; id = λ {c} → record
      { twiner = Category.id C
      ; in-tertwines = let x = F₀ (T.rendezvous c) in sym x (identity (refl x))
      ; out-ertwines = let x = G.₀ (T.rendezvous c) in sym x (G.identity (refl x)) }
    ; _∘_ = λ {a b c} f g → record
      { twiner = twiner f ∘ twiner g
      ; in-tertwines = let open SetoidR (F₀ (T.rendezvous c)) in
        begin
          T.in-side c
        ≈⟨ in-tertwines f ⟩
          F₁ (twiner f) ⟨$⟩ T.in-side b
        ≈⟨ F-resp-≈ Equiv.refl (in-tertwines g) ⟩
          F₁ (twiner f) ⟨$⟩ (F₁ (twiner g) ⟨$⟩ T.in-side a)
        ≈⟨ sym (F₀ (T.rendezvous c)) (homomorphism (refl (F₀ (T.rendezvous a)))) ⟩
          F₁ (twiner f ∘ twiner g) ⟨$⟩ T.in-side a
        ∎
      ; out-ertwines = let open SetoidR (G.₀ (T.rendezvous a)) in
        begin
          T.out-side a
        ≈⟨ out-ertwines g ⟩
          G.₁ (twiner g) ⟨$⟩ T.out-side b
        ≈⟨ G.F-resp-≈ Equiv.refl (out-ertwines f) ⟩
          G.₁ (twiner g) ⟨$⟩ (G.₁ (twiner f) ⟨$⟩ T.out-side c)
        ≈⟨ sym (G.₀ (T.rendezvous a)) (G.homomorphism (refl (G.₀ (T.rendezvous c)))) ⟩
          G.₁ (twiner f ∘ twiner g) ⟨$⟩ T.out-side c
        ∎
      }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
    ; ∘-resp-≈ = ∘-resp-≈
    }

  setoid = ST.setoid Twines (Category.id category)

-- this is the left adjoint to Disc : Setoids ⇒ Cats
Π₀ : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Setoids o (o ⊔ ℓ))
Π₀ = record
  { F₀ = λ C → ST.setoid (Category._⇒_ C) (Category.id C)
  ; F₁ = λ F → record
    { _⟨$⟩_ = Functor.F₀ F
    ; cong = ST.gmap (Functor.F₀ F) (Functor.F₁ F)
    }
  ; identity = λ x → x
  ; homomorphism = λ {_ _ _ F G} → ST.gmap (Functor.F₀ G ∙ Functor.F₀ F) (Functor.F₁ G ∙ Functor.F₁ F)
  ; F-resp-≈ = my-resp _ _
  }
  where
  my-resp : ∀ {A B : Category _ _ _} (f g : Functor A B) (f≅g : NaturalIsomorphism f g) {x y} → Plus⇔ (Category._⇒_ A) x y → Plus⇔ (Category._⇒_ B) (Functor.F₀ f x) (Functor.F₀ g y)
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.forth m) = Plus⇔.forth (B [ NaturalIsomorphism.⇒.η f≅g _ ∘ Functor.F₁ f m ])
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.back m) = Plus⇔.back (B [ Functor.F₁ f m ∘ NaturalIsomorphism.⇐.η f≅g _ ])
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.forth⁺ m ms) = Plus⇔.forth⁺ (B [ NaturalIsomorphism.⇒.η f≅g _ ∘ Functor.F₁ f m ]) (ST.gmap (Functor.F₀ g) (Functor.F₁ g) ms)
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.back⁺ m ms) = Plus⇔.back⁺ (B [ Functor.F₁ f m ∘ NaturalIsomorphism.⇐.η f≅g _ ]) (ST.gmap (Functor.F₀ g) (Functor.F₁ g) ms)

_ⓟ′_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C D) → Bifunctor (Category.op E) C (Cats (oD ⊔ ℓC ⊔ ℓD ⊔ ℓE ⊔ ℓP ⊔ ℓQ) (ℓD ⊔ eC ⊔ eD ⊔ eE ⊔ eP ⊔ eQ) (eD))
_ⓟ′_ {C = C} {D = D} {E = E} P Q = record
  { F₀ = my-F₀
  ; F₁ = my-F₁
  ; identity = my-identity
  ; homomorphism = my-homomorphism _ _ _ _
  ; F-resp-≈ = λ (e , c) → my-resp c e
  }
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E
  open FormalComposite.T

  my-F₀ : (Category.Obj E × Category.Obj C) → Category _ _ _
  my-F₀ (e , c) = FormalComposite.category D (appˡ P.bimodule e) (appʳ Q.bimodule c)
  my-F₁$ : ∀ {cA cB eA eB} → (E [ eB , eA ] × C [ cA , cB ]) → FormalComposite.T D (appˡ P.bimodule eA) (appʳ Q.bimodule cA) → FormalComposite.T D (appˡ P.bimodule eB) (appʳ Q.bimodule cB)
  my-F₁$ (g , f) x = record
    { rendezvous = rendezvous x
    ; in-side = P.₁ (g , D.id) ⟨$⟩ in-side x
    ; out-side = Q.₁ (D.id , f) ⟨$⟩ out-side x
    }
  my-F₁ : ∀ {cA cB eA eB} → (E [ eB , eA ] × C [ cA , cB ]) → Cats _ _ _ [ my-F₀ (eA , cA) , my-F₀ (eB , cB) ]
  my-F₁ (g , f) = record
    { F₀ = my-F₁$ (g , f)
    ; F₁ = λ {x y} h → record
      { twiner = FormalComposite.Twines.twiner h
      ; in-tertwines = let open SetoidR (P.₀ (_ , rendezvous y)) in
        begin
          P.₁ˡ g ⟨$⟩ in-side y
        ≈⟨ cong (P.₁ˡ g) (FormalComposite.Twines.in-tertwines h) ⟩
          P.₁ˡ g ⟨$⟩ (P.₁ʳ (FormalComposite.Twines.twiner h) ⟨$⟩ in-side x)
        ≈˘⟨ [ P.bimodule ]-commute (refl (P.₀ _)) ⟩
          P.₁ʳ (FormalComposite.Twines.twiner h) ⟨$⟩ (P.₁ˡ g ⟨$⟩ in-side x)
        ∎
      ; out-ertwines = let open SetoidR (Q.₀ (rendezvous x , _)) in
        begin
          Q.₁ʳ f ⟨$⟩ out-side x
        ≈⟨ cong (Q.₁ (D.id , f)) (FormalComposite.Twines.out-ertwines h) ⟩
          Q.₁ʳ f ⟨$⟩ (Q.₁ˡ (FormalComposite.Twines.twiner h) ⟨$⟩ out-side y)
        ≈⟨ [ Q.bimodule ]-commute (refl (Q.₀ _)) ⟩
          Q.₁ˡ (FormalComposite.Twines.twiner h) ⟨$⟩ (Q.₁ʳ f ⟨$⟩ out-side y)
        ∎
      }
    ; identity = D.Equiv.refl
    ; homomorphism = D.Equiv.refl
    ; F-resp-≈ = Function.id
    }
  my-identity : ∀ {c e} → Cats _ _ _ [ my-F₁ (E.id {e} , C.id {c}) ≈ Category.id (Cats _ _ _) ]
  my-identity {c} {e} = record
    { F⇒G = record
      { η = λ x → record
        { twiner = D.id
        ; in-tertwines = Setoid.sym (P.₀ _) (P.identity (P.identity (Setoid.refl (P.₀ _))))
        ; out-ertwines = Setoid.refl (Q.₀ _)
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; F⇐G = record
      { η = λ x → record
        { twiner = D.id
        ; in-tertwines = Setoid.refl (P.₀ _)
        ; out-ertwines = Setoid.sym (Q.₀ _) (Q.identity (Q.identity (Setoid.refl (Q.₀ _))))
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; iso = λ X → record
      { isoˡ = D.identity²
      ; isoʳ = D.identity²
      }
    }
  my-homomorphism : ∀ {cX cY cZ eX eY eZ} (cf : C [ cX , cY ]) (ef : E [ eY , eX ]) (cg : C [ cY , cZ ]) (eg : E [ eZ , eY ]) → Cats _ _ _ [ my-F₁ (E [ ef ∘ eg ] , C [ cg ∘ cf ]) ≈ Cats _ _ _ [ my-F₁ (eg , cg) ∘ my-F₁ (ef , cf) ] ]
  my-homomorphism {cX} {cY} {cZ} {eX} {eY} {eZ} cf ef cg eg = record
    { F⇒G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = let open SetoidR (P.₀ (eZ , rendezvous X)) in
          begin
            P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X)
          ≈˘⟨ P.homomorphismˡ (Setoid.refl (P.₀ _)) ⟩
            P.₁ˡ (E [ ef ∘ eg ]) ⟨$⟩ in-side X
          ≈˘⟨ P.identity (Setoid.refl (P.₀ _)) ⟩
            P.₁ʳ D.id ⟨$⟩ (P.₁ˡ (E [ ef ∘ eg ]) ⟨$⟩ in-side X)
          ∎
        ; out-ertwines = let open SetoidR (Q.₀ (rendezvous X , cZ)) in
          begin
            Q.₁ʳ (C [ cg ∘ cf ]) ⟨$⟩ out-side X
          ≈⟨ Q.homomorphismʳ (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ʳ cg ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ out-side X)
          ≈˘⟨ Q.identity (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ˡ D.id ⟨$⟩ (Q.₁ʳ cg ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ out-side X))
          ∎
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; F⇐G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = let open SetoidR (P.₀ (eZ , rendezvous X)) in
          begin
            P.₁ˡ (E [ ef ∘ eg ]) ⟨$⟩ in-side X
          ≈⟨ P.homomorphismˡ (Setoid.refl (P.₀ _)) ⟩
            P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X)
          ≈˘⟨ P.identity (Setoid.refl (P.₀ _)) ⟩
            P.₁ʳ D.id ⟨$⟩ (P.₁ˡ eg ⟨$⟩ (P.₁ˡ ef ⟨$⟩ in-side X))
          ∎
        ; out-ertwines = let open SetoidR (Q.₀ (rendezvous X , cZ)) in
          begin
            Q.₁ʳ cg ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ out-side X)
          ≈˘⟨ Q.homomorphismʳ (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ʳ (C [ cg ∘ cf ]) ⟨$⟩ out-side X
          ≈˘⟨ Q.identity (Setoid.refl (Q.₀ _)) ⟩
            Q.₁ˡ D.id ⟨$⟩ (Q.₁ʳ (C [ cg ∘ cf ]) ⟨$⟩ out-side X)
          ∎
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; iso = λ X → record { isoˡ = D.identity² ; isoʳ = D.identity² } }
  my-resp : ∀ {cA cB eA eB} {cf cg : C [ cA , cB ]} {ef eg : E [ eB , eA ]} → C [ cf ≈ cg ] → E [ ef ≈ eg ] → Cats _ _ _ [ my-F₁ (ef , cf) ≈ my-F₁ (eg , cg) ]
  my-resp {cA} {cB} {eA} {eB} {cf} {cg} {ef} {eg} cf≈cg ef≈eg = record
    { F⇒G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = Setoid.sym (P.₀ _) (P.identity (P.resp-≈ˡ ef≈eg (Setoid.refl (P.₀ _))))
        ; out-ertwines = Setoid.sym (Q.₀ _) (Q.identity (Q.resp-≈ʳ (C.Equiv.sym cf≈cg) (Setoid.refl (Q.₀ _))))
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; F⇐G = record
      { η = λ X → record
        { twiner = D.id
        ; in-tertwines = Setoid.sym (P.₀ _) (P.identity (P.resp-≈ˡ (E.Equiv.sym ef≈eg) (Setoid.refl (P.₀ _))))
        ; out-ertwines = Setoid.sym (Q.₀ _) (Q.identity (Q.resp-≈ʳ cf≈cg (Setoid.refl (Q.₀ _))))
        }
      ; commute = λ f → id-comm-sym D
      ; sym-commute = λ f → id-comm D
      }
    ; iso = λ X → record { isoˡ = D.identity² ; isoʳ = D.identity² }
    }

_ⓟ_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C D) → Profunctor (oD ⊔ ℓD ⊔ ℓP ⊔ ℓQ) (ℓC ⊔ oD ⊔ ℓD ⊔ eD ⊔ ℓE ⊔ ℓP ⊔ eP ⊔ ℓQ ⊔ eQ) C E
_ⓟ_ P Q = pro (Π₀ ∘F (P ⓟ′ Q))

_▻_ : ∀ {oC ℓC eC oD ℓD eD oE ℓE eE ℓP eP ℓQ eQ} {C : Category oC ℓC eC} {D : Category oD ℓD eD} {E : Category oE ℓE eE} (P : Profunctor ℓP eP D E) (Q : Profunctor ℓQ eQ C E) → Profunctor (oE ⊔ ℓE ⊔ ℓP ⊔ ℓQ ⊔ eC ⊔ eD ⊔ eE ⊔ eP ⊔ eQ) (oE ⊔ ℓC ⊔ ℓD ⊔ ℓE ⊔ ℓP ⊔ ℓQ ⊔ eE ⊔ eP ⊔ eQ) C D
_▻_ {oC} {ℓC} {eC} {oD} {ℓD} {eD} {oE} {ℓE} {eE} {ℓP} {eP} {ℓQ} {eQ} {C} {D} {E} P Q = pro (record
  { F₀ = λ (d , c) → Category.hom-setoid (Functors E.op (Setoids _ _)) {LiftSetoids (ℓC ⊔ ℓQ) (eC ⊔ eQ) ∘F appʳ P.bimodule d} {LiftSetoids (ℓD ⊔ ℓP) (eD ⊔ eP) ∘F appʳ Q.bimodule c}
  ; F₁ = λ (df , cf) → record
    { _⟨$⟩_ = λ ϕ → record
      { η = λ e → record
        { _⟨$⟩_ = λ m → lift (Q.₁ (E.id , cf) ⟨$⟩ lower (NaturalTransformation.η ϕ e ⟨$⟩ lift (P.₁ (E.id , df) ⟨$⟩ lower m)))
        ; cong = λ {i j} eq → lift (cong (Q.₁ (E.id , cf)) (lower (cong (NaturalTransformation.η ϕ e) (lift (cong (P.₁ (E.id , df)) (lower eq))))))
        }
      ; commute = λ {eX eY} ef {x y} x≈y → lift (let open SetoidR (Q.₀ _) in
        begin
          Q.₁ʳ cf ⟨$⟩ lower (NaturalTransformation.η ϕ eY ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ (P.₁ˡ ef ⟨$⟩ lower x)))
        ≈⟨ cong (Q.₁ʳ cf) (lower (cong (NaturalTransformation.η ϕ eY) (lift (cong (P.₁ʳ df) (cong (P.₁ˡ ef) (lower x≈y)))))) ⟩
          Q.₁ʳ cf ⟨$⟩ lower (NaturalTransformation.η ϕ eY ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ (P.₁ˡ ef ⟨$⟩ lower y)))
        ≈⟨ cong (Q.₁ʳ cf) (lower (cong (NaturalTransformation.η ϕ eY) (lift ([ P.bimodule ]-commute (Setoid.refl (P.₀ _)))))) ⟩
          Q.₁ʳ cf ⟨$⟩ lower (NaturalTransformation.η ϕ eY ⟨$⟩ lift (P.₁ˡ ef ⟨$⟩ (P.₁ʳ df ⟨$⟩ lower y)))
        ≈⟨ cong (Q.₁ʳ cf) (lower (NaturalTransformation.commute ϕ ef (lift (Setoid.refl (P.₀ _))))) ⟩
          Q.₁ʳ cf ⟨$⟩ (Q.₁ˡ ef ⟨$⟩ (lower (NaturalTransformation.η ϕ eX ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ lower y))))
        ≈⟨ [ Q.bimodule ]-commute (Setoid.refl (Q.₀ _)) ⟩
          Q.₁ˡ ef ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ (lower (NaturalTransformation.η ϕ eX ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ lower y))))
        ∎)
      ; sym-commute = λ {eX eY} ef {x y} x≈y → lift (let open SetoidR (Q.₀ _) in
        begin
          Q.₁ˡ ef ⟨$⟩ (Q.₁ʳ cf ⟨$⟩ (lower (NaturalTransformation.η ϕ eX ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ lower x))))
        ≈˘⟨ [ Q.bimodule ]-commute (Setoid.refl (Q.₀ _)) ⟩
          Q.₁ʳ cf ⟨$⟩ (Q.₁ˡ ef ⟨$⟩ (lower (NaturalTransformation.η ϕ eX ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ lower x))))
        ≈˘⟨ cong (Q.₁ʳ cf) (lower (NaturalTransformation.commute ϕ ef (lift (Setoid.refl (P.₀ _))))) ⟩
          Q.₁ʳ cf ⟨$⟩ lower (NaturalTransformation.η ϕ eY ⟨$⟩ lift (P.₁ˡ ef ⟨$⟩ (P.₁ʳ df ⟨$⟩ lower x)))
        ≈˘⟨ cong (Q.₁ʳ cf) (lower (cong (NaturalTransformation.η ϕ eY) (lift ([ P.bimodule ]-commute (Setoid.refl (P.₀ _)))))) ⟩
          Q.₁ʳ cf ⟨$⟩ lower (NaturalTransformation.η ϕ eY ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ (P.₁ˡ ef ⟨$⟩ lower x)))
        ≈⟨ cong (Q.₁ʳ cf) (lower (cong (NaturalTransformation.η ϕ eY) (lift (cong (P.₁ʳ df) (cong (P.₁ˡ ef) (lower x≈y)))))) ⟩
          Q.₁ʳ cf ⟨$⟩ lower (NaturalTransformation.η ϕ eY ⟨$⟩ lift (P.₁ʳ df ⟨$⟩ (P.₁ˡ ef ⟨$⟩ lower y)))
        ∎)
      }
    ; cong = λ {σ τ} σ≈τ {e x y} x≈y → lift (cong (Q.₁ʳ cf) (lower (σ≈τ (lift (cong (P.₁ʳ df) (lower x≈y))))))
    }
  ; identity = λ {(d , c)} {σ τ} σ≈τ {e x y} x≈y → lift (Q.identity (lower (σ≈τ (lift (P.identity (lower x≈y))))))
  ; homomorphism = λ {(dX , cX) (dY , cY) (dZ , cZ) (df , cf) (dg , cg) σ τ} σ≈τ {e x y} x≈y → lift (Q.homomorphismʳ (lower (σ≈τ (lift (P.homomorphismʳ (lower x≈y))))))
  ; F-resp-≈ = λ {(dA , cA) (dB , cB) (df , cf) (dg , cg)} (df≈dg , cf≈cg) {σ τ} σ≈τ {e x y} x≈y → lift (Q.resp-≈ʳ cf≈cg (lower (σ≈τ (lift (P.resp-≈ʳ df≈dg (lower x≈y))))))
  })
  where
  module P = Profunctor P
  module Q = Profunctor Q
  module C = Category C
  module D = Category D
  module E = Category E
