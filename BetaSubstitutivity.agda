open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Fin using (zero; suc)
open import Data.Nat using (suc)

open import Substitution using (rename-subst-commute; subst-commute)
open import DeBruijn
open import Beta


infix 3 _—↠ˢ_

_—↠ˢ_ : ∀ {n m} → Subst n m → Subst n m → Set
σ —↠ˢ σ′ = ∀ {x} → σ x —↠ σ′ x


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
betas-rename {ρ = ρ} (M —→⟨ M—→L ⟩ L—↠M′) = rename ρ M —→⟨ beta-rename M—→L ⟩ betas-rename L—↠M′


betas-subst-exts : ∀ {n m} {σ σ′ : Subst n m}
  → σ —↠ˢ σ′
    ------------------
  → exts σ —↠ˢ exts σ′
betas-subst-exts σ—↠σ′ {zero}  = # zero ∎
betas-subst-exts σ—↠σ′ {suc x} = betas-rename σ—↠σ′


subst-betas-sub : ∀ {n m} {M : Term n} {σ σ′ : Subst n m}
  → σ —↠ˢ σ′
    -----------------------
  → subst σ M —↠ subst σ′ M
subst-betas-sub {M = # x}   σ—↠σ′ = σ—↠σ′
subst-betas-sub {M = M · N} σ—↠σ′ = —↠-cong (subst-betas-sub {M = M} σ—↠σ′)
                                            (subst-betas-sub {M = N} σ—↠σ′)
subst-betas-sub {M = ƛ M}   σ—↠σ′ =
  —↠-cong-ƛ (subst-betas-sub {M = M} (λ {x} → betas-subst-exts σ—↠σ′ {x = x}))


subst-beta-term : ∀ {n m} {M M′ : Term n} {σ : Subst n m}
  → M —→ M′
    -----------------------
  → subst σ M —→ subst σ M′
subst-beta-term (—→-ƛ  M—→M′) = —→-ƛ  (subst-beta-term M—→M′)
subst-beta-term (—→-ξₗ M—→M′) = —→-ξₗ (subst-beta-term M—→M′)
subst-beta-term (—→-ξᵣ N—→N′) = —→-ξᵣ (subst-beta-term N—→N′)
subst-beta-term {σ = σ} (—→-β {M = M}{N = N})
  rewrite sym (subst-commute {N = M}{M = N}{σ = σ}) = —→-β


subst-betas : ∀ {n m} {σ σ′ : Subst n m} {M M′ : Term n}
  → σ —↠ˢ σ′
  → M —↠ M′
    ------------------------
  → subst σ M —↠ subst σ′ M′
subst-betas σ—↠σ′ (M ∎) = subst-betas-sub {M = M} σ—↠σ′
subst-betas {σ = σ} σ—↠σ′ (M —→⟨ M—→L ⟩ L—↠M′) =
  subst σ M —→⟨ subst-beta-term M—→L ⟩ subst-betas σ—↠σ′ L—↠M′


betas-subst-zero : ∀ {n} {M M′ : Term n}
  → M —↠ M′
    ------------------------------
  → subst-zero M —↠ˢ subst-zero M′
betas-subst-zero M—↠M′ {zero}  = M—↠M′
betas-subst-zero M—↠M′ {suc x} = # x ∎


sub-betas : ∀ {n} {M M′ : Term (suc n)} {N N′ : Term n}
  → M —↠ M′
  → N —↠ N′
    --------------------
  → M [ N ] —↠ M′ [ N′ ]
sub-betas M—↠M′ N—↠N′ = subst-betas (betas-subst-zero N—↠N′) M—↠M′
