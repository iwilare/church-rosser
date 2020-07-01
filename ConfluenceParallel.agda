open import Data.Product using (∃; ∃-syntax; _×_; _,_)

open import DeBruijn
open import Parallel
open import Beta


par-diamond : ∀ {n} {M N N′ : Term n}
  →         M ⇉ N → M  ⇉ N′
    -----------------------
  → ∃[ L ] (N ⇉ L × N′ ⇉ L)
par-diamond (⇉-c {x = x}) ⇉-c = # x ,  ⇉-c , ⇉-c
par-diamond (⇉-ƛ p1) (⇉-ƛ p2)
    with par-diamond p1 p2
... | L′ , p3 , p4 =
      ƛ L′ , ⇉-ƛ p3 , ⇉-ƛ p4
par-diamond (⇉-ξ p1 p3) (⇉-ξ p2 p4)
    with par-diamond p1 p2
... | L₃ , p5 , p6
      with par-diamond p3 p4
...   | M₃ , p7 , p8 =
        L₃ · M₃ , ⇉-ξ p5 p7 , ⇉-ξ p6 p8
par-diamond (⇉-ξ (⇉-ƛ p1) p3) (⇉-β p2 p4)
    with par-diamond p1 p2
... | N₃ , p5 , p6
      with par-diamond p3 p4
...   | M₃ , p7 , p8 =
        N₃ [ M₃ ] , ⇉-β p5 p7 , sub-par p6 p8
par-diamond (⇉-β p1 p3) (⇉-ξ (⇉-ƛ p2) p4)
    with par-diamond p1 p2
... | N₃ , p5 , p6
      with par-diamond p3 p4
...   | M₃ , p7 , p8 =
        N₃ [ M₃ ] , sub-par p5  p7 , ⇉-β p6 p8
par-diamond (⇉-β p1 p3) (⇉-β p2 p4)
    with par-diamond p1 p2
... | N₃ , p5 , p6
      with par-diamond p3 p4
...   | M₃ , p7 , p8 =
        N₃ [ M₃ ] , sub-par p5 p7 , sub-par p6 p8


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
