module Categories.Functor.Dense where

open import Categories.Category
open import Categories.Functor

record IsDense :

∀ c, C(c,lim^W F(-)) ≅ [K,V](W(-,─), C(c, F(─)))
∀ c, C(W ∙ F(-),c) ≅ [J^{op},V](W(─,-), C(F(─), c))

C(ℓ,1) ≅ W ⊳ C(f,1)  -- colimit
