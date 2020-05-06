open import Data.Product using (∃; ∃-syntax; _×_; _,_)

open import DeBruijn
open import Parallel
open import Beta
open import Takahashi


theorem5 : ∀ {n} {M N : Term n}
  → M ⇉ N
    -------
  → N ⇉ M *
theorem5 {M = # x} ⇉-c = ⇉-c
theorem5 {M = ƛ M} (⇉-ƛ M⇉N) = ⇉-ƛ (theorem5 M⇉N)
theorem5 {M = (ƛ M) · N} (⇉-β M⇉M′ N⇉N′) = sub-par (theorem5 M⇉M′) (theorem5 N⇉N′)
theorem5 {M = # _     · N} (⇉-ξ M⇉M′ N⇉N′)       = ⇉-ξ (theorem5 M⇉M′) (theorem5 N⇉N′)
theorem5 {M = M₁ · M₂ · N} (⇉-ξ M⇉M′ N⇉N′)       = ⇉-ξ (theorem5 M⇉M′) (theorem5 N⇉N′)
theorem5 {M = (ƛ M)   · N} (⇉-ξ (⇉-ƛ M⇉M′) N⇉N′) = ⇉-β (theorem5 M⇉M′) (theorem5 N⇉N′)


par-diamond : ∀ {n} {M M₁ M₂ : Term n}
  →          M  ⇉ M₁  → M  ⇉ M₂
    ----------------------------
  → ∃[ N ] ((M₁ ⇉ N) × (M₂ ⇉ N))
par-diamond {M = M} M⇉M₁ M⇉M₂ = M * , theorem5 M⇉M₁ , theorem5 M⇉M₂


strip : ∀ {n} {M A B : Term n}
  →          M ⇉  A  →  M ⇉* B
    ----------------------------
  → ∃[ N ] ((A ⇉* N) × (B ⇉  N))
strip {A = A} M⇉A (M ∎) = A , (A ∎) , M⇉A
strip {A = A} M⇉A (M ⇉⟨　M⇉M′ ⟩ M′⇉*B)
    with par-diamond M⇉A M⇉M′
... | N , A⇉N , M′⇉N
      with strip M′⇉N M′⇉*B
...   | N′ , N⇉*N′              , B⇉N′ =
        N′ , (A ⇉⟨ A⇉N ⟩ N⇉*N′) , B⇉N′


par-confluence : ∀ {n} {M A B : Term n}
  →          M ⇉* A  →  M ⇉* B
    ----------------------------
  → ∃[ N ] ((A ⇉* N) × (B ⇉* N))
par-confluence {B = B} (M ∎) M⇉*B = B , M⇉*B , (B ∎)
par-confluence {B = B} (M ⇉⟨ M⇉A ⟩ A⇉*A′) M⇉*B
    with strip M⇉A M⇉*B
... | N , A⇉*N , B⇉N
      with par-confluence A⇉*A′ A⇉*N
...   | N′ , A′⇉*N′ , N⇉*N′ =
        N′ , A′⇉*N′ , (B ⇉⟨ B⇉N ⟩ N⇉*N′)


confluence : ∀ {n} {M M₁ M₂ : Term n}
  →          M  —↠ M₁ →  M  —↠ M₂
    ------------------------------
  → ∃[ N ] ((M₁ —↠ N) × (M₂ —↠ N))
confluence M—↠M₁ M—↠M₂
    with par-confluence (betas-pars M—↠M₁) (betas-pars M—↠M₂)
... | N , M₁⇉*N , M₂⇉*N =
      N , pars-betas M₁⇉*N , pars-betas M₂⇉*N
