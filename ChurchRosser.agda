open import Data.Product
open import DeBruijn
open import Substitution
open import Parallel
open import Beta


infix 8 _*

_* : ∀ {n} → Term n → Term n
(# x) *       = # x
(ƛ M) *       = ƛ M *
((ƛ M) · N) * = M * [ N * ]
(L · N) *     = L * · N *


theorem5 : ∀{n} {M N : Term n}
  → M ⇉ N
    -------
  → N ⇉ M *
theorem5 {M = # x} ⇉-c = ⇉-c
theorem5 {M = ƛ M} (⇉-ƛ M⇉N) = ⇉-ƛ (theorem5 M⇉N)
theorem5 {M = (ƛ M) · N} (⇉-β M⇉M′ N⇉N′) = sub-par (theorem5 M⇉M′) (theorem5 N⇉N′)

{-
  Agda non riesce a capire che M · N non è una β-reduct per quindi poter
  applicare L * · M * ≡ (L · M) *, pur essendo l′unica possibilità dato
  che il caso con L = ƛ x ⇒ x₁ è trattato separatamente.
  Bisogna per questo fare case-splitting sul primo termine e analizzare caso per caso.
-}

theorem5 {M = # _     · N} (⇉-ξ M⇉M′ N⇉N′)       = ⇉-ξ (theorem5 M⇉M′) (theorem5 N⇉N′)
theorem5 {M = (ƛ M)   · N} (⇉-ξ (⇉-ƛ M⇉M′) N⇉N′) = ⇉-β (theorem5 M⇉M′) (theorem5 N⇉N′)
theorem5 {M = M₁ · M₂ · N} (⇉-ξ M⇉M′ N⇉N′)       = ⇉-ξ (theorem5 M⇉M′) (theorem5 N⇉N′)


confluent⇉ : ∀{n} {M M₁ M₂ : Term n}
  →          M ⇉ M₁  →  M ⇉ M₂
    --------------------------
  → ∃[ N ] ((M₁ ⇉ N) × (M₂ ⇉ N))
confluent⇉ {M = M} M⇉M₁ M⇉M₂ = M * , theorem5 M⇉M₁ , theorem5 M⇉M₂


strip : ∀{n} {M A B : Term n}
  →          M ⇉  A  →  M ⇉* B
    ----------------------------
  → ∃[ N ] ((A ⇉* N) × (B ⇉  N))
strip{n}{M}{A} mn (_ ∎) = A , (A ∎) , mn
strip{n}{M}{A} mn (M ⇉⟨ mm' ⟩ m'n')
    with confluent⇉ mn mm'
... | N , nl , m'l
      with strip m'l m'n'
...   | N′ , ll'             , n'l' =
        N′ , (A ⇉⟨ nl ⟩ ll') , n'l'


confluent⇉* : ∀{n} {M A B : Term n}
  →          M ⇉* A  →  M ⇉* B
    ------------------------------
  → ∃[ N ] ((A ⇉* N) × (B ⇉* N))
confluent⇉* {B = N} (M ∎) M⇉*N = N , M⇉*N , (N ∎)
confluent⇉* {B = B} (M ⇉⟨ M⇉A ⟩ A⇉*A′) M⇉*B
    with strip M⇉A M⇉*B
... | N , A⇉*N , B⇉N
      with confluent⇉* A⇉*A′ A⇉*N
...   | N′ , A′⇉*N′ , N⇉*N′ =
        N′ , A′⇉*N′ , (B ⇉⟨ B⇉N ⟩ N⇉*N′)


confluent—↠ : ∀{n} {M M₁ M₂ : Term n}
  →          M  —↠ M₁ →  M  —↠ M₂
    ------------------------------
  → ∃[ N ] ((M₁ —↠ N) × (M₂ —↠ N))
confluent—↠ M—↠M₁ M—↠M₂
    with confluent⇉* (betas-pars M—↠M₁) (betas-pars M—↠M₂)
... | N , M₁⇉N , M₂⇉N =
      N , pars-betas M₁⇉N , pars-betas M₂⇉N
