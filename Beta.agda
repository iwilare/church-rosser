open import Data.Nat using (suc)

open import Substitution using (rename-subst-commute; subst-commute)
open import DeBruijn


infix 2 _—→_

data _—→_ : ∀ {n} → Term n → Term n → Set where

  —→-ξₗ : ∀ {n} {M M′ N : Term n}
    → M —→ M′
      ---------------
    → M · N —→ M′ · N

  —→-ξᵣ : ∀ {n} {M N N′ : Term n}
    → N —→ N′
      ---------------
    → M · N —→ M · N′

  —→-β : ∀ {n} {M : Term (suc n)} {N : Term n}
      --------------------
    → (ƛ M) · N —→ M [ N ]

  —→-ƛ : ∀ {n} {M M′ : Term (suc n)}
    → M —→ M′
      -----------
    → ƛ M —→ ƛ M′


infix  2 _—↠_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {n} {L N : Term n} (M : Term n)
    → M —→ L
    → L —↠ N
      ------
    → M —↠ N


—↠-trans : ∀ {n} {M L N : Term n}
  → M —↠ L
  → L —↠ N
    ------
  → M —↠ N
—↠-trans (M ∎)                 M—↠M = M—↠M
—↠-trans (M —→⟨ M—→L′ ⟩ L′—↠L) L—↠N = M —→⟨ M—→L′ ⟩ (—↠-trans L′—↠L L—↠N )


—↠-congₗ : ∀ {n} {M M′ R : Term n}
  → M —↠ M′
    ---------------
  → M · R —↠ M′ · R
—↠-congₗ {M = M}{R = R} (M ∎)                = M · R ∎
—↠-congₗ {M = M}{R = R} (M —→⟨ M—→L ⟩ L—↠M′) = M · R —→⟨ —→-ξₗ M—→L ⟩ —↠-congₗ L—↠M′


—↠-congᵣ : ∀ {n} {M M′ L : Term n}
  → M —↠ M′
    ---------------
  → L · M —↠ L · M′
—↠-congᵣ {M = M}{L = L} (M ∎)                = L · M ∎
—↠-congᵣ {M = M}{L = L} (M —→⟨ M—→L ⟩ L—↠M′) = L · M —→⟨ —→-ξᵣ M—→L ⟩ —↠-congᵣ L—↠M′


—↠-cong-ƛ : ∀ {n} {M M′ : Term (suc n)}
  → M —↠ M′
    -----------
  → ƛ M —↠ ƛ M′
—↠-cong-ƛ (M ∎)                = ƛ M ∎
—↠-cong-ƛ (M —→⟨ M—→L ⟩ L—↠N′) = ƛ M —→⟨ —→-ƛ M—→L ⟩ —↠-cong-ƛ L—↠N′


—↠-cong : ∀ {n} {M M′ N N′ : Term n}
  → M —↠ M′
  → N —↠ N′
    ----------------
  → M · N —↠ M′ · N′
—↠-cong M—↠M′ N—↠N′ = —↠-trans (—↠-congₗ M—↠M′) (—↠-congᵣ N—↠N′)
