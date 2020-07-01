open import Data.Product using (∃; ∃-syntax; _×_; _,_)

open import DeBruijn
open import Parallel
open import Beta
open import Takahashi


par-triangle : ∀ {n} {M N : Term n}
  → M ⇉ N
    -------
  → N ⇉ M *
par-triangle {M = # x} ⇉-c = ⇉-c
par-triangle {M = ƛ M} (⇉-ƛ M⇉N) = ⇉-ƛ (par-triangle M⇉N)
par-triangle {M = (ƛ M) · N} (⇉-β M⇉M′ N⇉N′) = sub-par (par-triangle M⇉M′) (par-triangle N⇉N′)
par-triangle {M = # _   · N} (⇉-ξ M⇉M′ N⇉N′)       = ⇉-ξ (par-triangle M⇉M′) (par-triangle N⇉N′)
par-triangle {M = _ · _ · N} (⇉-ξ M⇉M′ N⇉N′)       = ⇉-ξ (par-triangle M⇉M′) (par-triangle N⇉N′)
par-triangle {M = (ƛ _) · N} (⇉-ξ (⇉-ƛ M⇉M′) N⇉N′) = ⇉-β (par-triangle M⇉M′) (par-triangle N⇉N′)


par-diamond : ∀ {n} {M A B : Term n}
  →         M ⇉ A → M ⇉ B
    ----------------------
  → ∃[ N ] (A ⇉ N × B ⇉ N)
par-diamond {M = M} M⇉A M⇉B = M * , par-triangle M⇉A , par-triangle M⇉B


strip : ∀ {n} {M A B : Term n}
  →         M ⇉  A → M ⇉* B
    ------------------------
  → ∃[ N ] (A ⇉* N × B ⇉  N)
strip {A = A} M⇉A (M ∎) = A , (A ∎) , M⇉A
strip {A = A} M⇉A (M ⇉⟨　M⇉M′ ⟩ M′⇉*B)
    with par-diamond M⇉A M⇉M′
... | N , A⇉N , M′⇉N
      with strip M′⇉N M′⇉*B
...   | N′ , N⇉*N′              , B⇉N′ =
        N′ , (A ⇉⟨ A⇉N ⟩ N⇉*N′) , B⇉N′


par-confluence : ∀ {n} {M A B : Term n}
  →         M ⇉* A → M ⇉* B
    ------------------------
  → ∃[ N ] (A ⇉* N × B ⇉* N)
par-confluence {B = B} (M ∎) M⇉*B = B , M⇉*B , (B ∎)
par-confluence {B = B} (M ⇉⟨ M⇉A ⟩ A⇉*A′) M⇉*B
    with strip M⇉A M⇉*B
... | N , A⇉*N , B⇉N
      with par-confluence A⇉*A′ A⇉*N
...   | N′ , A′⇉*N′ , N⇉*N′ =
        N′ , A′⇉*N′ , (B ⇉⟨ B⇉N ⟩ N⇉*N′)


confluence : ∀ {n} {M A B : Term n}
  →         M —↠ A → M —↠ B
    ------------------------
  → ∃[ N ] (A —↠ N × B —↠ N)
confluence M—↠A M—↠B
    with par-confluence (betas-pars M—↠A) (betas-pars M—↠B)
... | N , A⇉*N , B⇉*N =
      N , pars-betas A⇉*N , pars-betas B⇉*N
