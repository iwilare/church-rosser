import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst₂; cong₂; sym)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import DeBruijn
open import Substitution

infix 2 _—→_

data _—→_ : ∀ {n} → Term n → Term n → Set where

  —→-ξₗ : ∀ {n} {M M′ N : Term n}
    → M —→ M′
      ---------------
    → M · N —→ M′ · N

  —→-ξᵣ : ∀ {n} {M N N′ : Term n}
    → N —→ N′
      ----------------
    → M · N —→ M · N′

  —→-β : ∀ {n} {M : Term (suc n)} {N : Term n}
      ---------------------------------
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

  _—→⟨_⟩_ : ∀ {n} {N T : Term n} (M : Term n)
    → M —→ T
    → T —↠ N
      ------
    → M —↠ N


—↠-trans : ∀{n} {M N T : Term n}
  → M —↠ T
  → T —↠ N
    ------
  → M —↠ N
—↠-trans (M ∎)                 M—↠M = M—↠M
—↠-trans (M —→⟨ M—→T′ ⟩ T′—↠T) T—↠N = M —→⟨ M—→T′ ⟩ (—↠-trans T′—↠T T—↠N )


—↠-congₗ : ∀ {n} {M M′ R : Term n}
  → M —↠ M′
    ---------------
  → M · R —↠ M′ · R
—↠-congₗ {M = M}{R = R} (M ∎)                = M · R ∎
—↠-congₗ {M = M}{R = R} (M —→⟨ M—→T ⟩ T—↠M′) = M · R —→⟨ —→-ξₗ M—→T ⟩ —↠-congₗ T—↠M′


—↠-congᵣ : ∀ {n} {M M′ L : Term n}
  → M —↠ M′
    ---------------
  → L · M —↠ L · M′
—↠-congᵣ {M = M}{L = L} (M ∎)                = L · M ∎
—↠-congᵣ {M = M}{L = L} (M —→⟨ M—→T ⟩ T—↠M′) = L · M —→⟨ —→-ξᵣ M—→T ⟩ —↠-congᵣ T—↠M′


—↠-ƛ-cong : ∀ {n} {M M′ : Term (suc n)}
  → M —↠ M′
    -----------
  → ƛ M —↠ ƛ M′
—↠-ƛ-cong (M ∎)                = ƛ M ∎
—↠-ƛ-cong (M —→⟨ M—→T ⟩ T—↠N′) = ƛ M —→⟨ —→-ƛ M—→T ⟩ —↠-ƛ-cong T—↠N′


—↠-cong : ∀ {n} {M M′ N N′ : Term n}
  → M —↠ M′
  → N —↠ N′
    ----------------
  → M · N —↠ M′ · N′
—↠-cong M—↠M′ N—↠N′ = —↠-trans (—↠-congₗ M—↠M′) (—↠-congᵣ N—↠N′)


betas-subst : ∀ {n m} → Subst n m → Subst n m → Set
betas-subst {n}{m} σ σ′ = ∀ {x : Fin n} → σ x —↠ σ′ x

beta-subst : ∀ {n m} → Subst n m → Subst n m → Set
beta-subst {n}{m} σ σ′ = ∀ {x : Fin n} → σ x —→ σ′ x


beta-rename : ∀ {n m} {ρ : Rename n m} {M M′ : Term n}
  → M —→ M′
    -------------------------
  → rename ρ M —→ rename ρ M′
beta-rename (—→-ƛ  M—→M′)  = —→-ƛ (beta-rename M—→M′)
beta-rename (—→-ξₗ M—→M′) = —→-ξₗ (beta-rename M—→M′)
beta-rename (—→-ξᵣ N—→N′) = —→-ξᵣ (beta-rename N—→N′)
beta-rename {ρ = ρ} (—→-β {M = M}{N = N})
  rewrite sym (rename-subst-commute {N = M}{M = N}{ρ = ρ}) = —→-β


betas-rename : ∀ {n m} {ρ : Rename n m} {M M′ : Term n}
  → M —↠ M′
    -------------------------
  → rename ρ M —↠ rename ρ M′
betas-rename {ρ = ρ} (M ∎)                = rename ρ M ∎
betas-rename {ρ = ρ} (M —→⟨ M—→T ⟩ T—↠M′) = rename ρ M —→⟨ beta-rename M—→T ⟩ betas-rename T—↠M′


betas-subst-exts : ∀ {n m} {σ τ : Subst n m}
  → betas-subst σ τ
    -----------------------------
  → betas-subst (exts σ) (exts τ)
betas-subst-exts σ—↠τ {zero}  = # zero ∎
betas-subst-exts σ—↠τ {suc x} = betas-rename σ—↠τ


subst-betas-base : ∀ {n m} {M : Term n} {σ τ : Subst n m}
  → betas-subst σ τ
    ----------------------
  → subst σ M —↠ subst τ M
subst-betas-base {M = # x}   σ—↠τ = σ—↠τ
subst-betas-base {M = N · M} σ—↠τ = —↠-cong   (subst-betas-base {M = N} σ—↠τ)
                                              (subst-betas-base {M = M} σ—↠τ)
subst-betas-base {M = ƛ M}   σ—↠τ =
  —↠-ƛ-cong (subst-betas-base {M = M}
               (λ {x} → betas-subst-exts σ—↠τ {x = x}))


subst-beta-direct : ∀ {n m} {M M′ : Term n} {σ : Subst n m}
  → M —→ M′
    -----------------------
  → subst σ M —→ subst σ M′
subst-beta-direct (—→-ƛ  M—→M′) = —→-ƛ  (subst-beta-direct M—→M′)
subst-beta-direct (—→-ξₗ M—→M′) = —→-ξₗ (subst-beta-direct M—→M′)
subst-beta-direct (—→-ξᵣ N—→N′) = —→-ξᵣ (subst-beta-direct N—→N′)
subst-beta-direct {σ = σ} (—→-β {M = M}{N = N})
  rewrite sym (subst-commute {N = M}{M = N}{σ = σ}) = —→-β


subst-betas : ∀ {n m} {σ τ : Subst n m} {M M′ : Term n}
  → betas-subst σ τ
  → M —↠ M′
    -----------------------
  → subst σ M —↠ subst τ M′
subst-betas σ—↠τ (M ∎) = subst-betas-base {M = M} σ—↠τ
subst-betas {σ = σ} σ—↠τ (M —→⟨ M—→T ⟩ T—↠M′) =
  subst σ M —→⟨ subst-beta-direct M—→T ⟩ subst-betas σ—↠τ T—↠M′


betas-subst-zero : ∀ {n} {M M′ : Term n}
  → M —↠ M′
    ------------------------------------------
  → betas-subst (subst-zero M) (subst-zero M′)
betas-subst-zero M—↠M′ {zero}  = M—↠M′
betas-subst-zero M—↠M′ {suc x} = # x ∎


sub-betas : ∀ {n} {M M′ : Term (suc n)} {N N′ : Term n}
  → M —↠ M′
  → N —↠ N′
    --------------------
  → M [ N ] —↠ M′ [ N′ ]
sub-betas M—↠M′ N—↠N′ = subst-betas (betas-subst-zero N—↠N′) M—↠M′


beta-complete : ∀ {n} {N N′ : Term (suc n)} {M M′ : Term n}
  → N —↠ N′
  → M —↠ M′
    ----------------------
  → (ƛ N) · M —↠ N′ [ M′ ]
beta-complete {N = N}{M = M} N—↠N′ M—↠M′ = (ƛ N) · M —→⟨ —→-β ⟩ (sub-betas N—↠N′ M—↠M′)
