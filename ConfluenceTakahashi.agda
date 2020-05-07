open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-total)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (∃; ∃-syntax; _×_; _,_)
open import Data.Sum using ([_,_])

open import DeBruijn
open import Substitution
open import Beta
open import BetaProperties using (sub-betas)
open import Takahashi


infix 5 _*⁽_⁾

_*⁽_⁾ : ∀ {n} → Term n → ℕ → Term n
M *⁽ zero ⁾  = M
M *⁽ suc k ⁾ = (M *) *⁽ k ⁾


data _—↠⁽_⁾_ : ∀ {n} → Term n → ℕ → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      --------------
    → M —↠⁽ zero ⁾ M

  _—→⁽⁾⟨_⟩_ : ∀ {n} {N L : Term n} {k : ℕ} (M : Term n)
    → M —→ L
    → L —↠⁽ k ⁾ N
      ---------------
    → M —↠⁽ suc k ⁾ N


lemma3-2 : ∀ {n} {M : Term n}
  → M —↠ M *
lemma3-2 {M = # x}       = # x ∎
lemma3-2 {M = ƛ _}       = —↠-cong-ƛ lemma3-2
lemma3-2 {M = # _ · _}   = —↠-congᵣ  lemma3-2
lemma3-2 {M = _ · _ · _} = —↠-cong   lemma3-2 lemma3-2
lemma3-2 {M = (ƛ M) · N} = (ƛ M) · N —→⟨ —→-β ⟩ sub-betas {M = M} lemma3-2 lemma3-2


lemma3-3 : ∀ {n} {M N : Term n}
  → M —→ N
    --------
  → N —↠ M *
lemma3-3 {M = # _} ()
lemma3-3 {M = ƛ M}         (—→-ƛ M—→M′)  = —↠-cong-ƛ (lemma3-3 M—→M′)
lemma3-3 {M = # _     · N} (—→-ξᵣ N—→N′) = —↠-congᵣ  (lemma3-3 N—→N′)
lemma3-3 {M = _ · _   · N} (—→-ξᵣ N—→N′) = —↠-cong  lemma3-2       (lemma3-3 N—→N′)
lemma3-3 {M = M₁ · M₂ · _} (—→-ξₗ M—↠M′) = —↠-cong (lemma3-3 M—↠M′) lemma3-2
lemma3-3 {M = (ƛ M)   · N}  —→-β         = sub-betas {M = M} lemma3-2 lemma3-2
lemma3-3 {M = (ƛ M)   · N} (—→-ξᵣ       {N′ = N′} N—→N′)  = (ƛ M ) · N′ —→⟨ —→-β ⟩ sub-betas {M = M} lemma3-2 (lemma3-3 N—→N′)
lemma3-3 {M = (ƛ M)   · N} (—→-ξₗ (—→-ƛ {M′ = M′} M—→M′)) = (ƛ M′) · N  —→⟨ —→-β ⟩ sub-betas {N = N} (lemma3-3 M—→M′) lemma3-2


app-*-join : ∀ {n} (M N : Term n)
  → M * · N * —↠ (M · N) *
app-*-join (# x)     N = # x · N * ∎
app-*-join (ƛ M)     N = (ƛ M *) · N * —→⟨ —→-β ⟩ subst (subst-zero (N *)) (M *) ∎
app-*-join (M₁ · M₂) N = (M₁ · M₂) * · N * ∎


rename-* : ∀ {n m} (ρ : Rename n m) (M : Term n)
  → rename ρ (M *) ≡ (rename ρ M) *
rename-* ρ (# _)         = refl
rename-* ρ (ƛ M)         = cong ƛ_ (rename-* (ext ρ) M)
rename-* ρ (# _     · N) = cong₂ _·_ refl                   (rename-* ρ N)
rename-* ρ (M₁ · M₂ · N) = cong₂ _·_ (rename-* ρ (M₁ · M₂)) (rename-* ρ N)
rename-* ρ ((ƛ M)   · N) rewrite sym (rename-subst-commute {N = M *}{M = N *}{ρ = ρ})
                               | rename-* (ext ρ) M
                               | rename-* ρ N
                               = refl


_*ˢ : ∀ {n m} (σ : Subst n m) → Subst n m
_*ˢ σ = λ x → (σ x) *


rename-suc-ts : ∀ {n m} (σ : Subst n m) (x : Fin n)
  → rename suc ((σ *ˢ) x) ≡ ((exts σ) *ˢ) (suc x)
rename-suc-ts σ x with σ x
rename-suc-ts σ x | # _         = refl
rename-suc-ts σ x | ƛ M         = cong ƛ_ (rename-* (ext suc) M)
rename-suc-ts σ x | # _     · N = cong₂ _·_ refl                     (rename-* suc N)
rename-suc-ts σ x | M₁ · M₂ · N = cong₂ _·_ (rename-* suc (M₁ · M₂)) (rename-* suc N)
rename-suc-ts σ x | (ƛ M)   · N rewrite sym (rename-subst-commute {N = M *}{M = N *}{ρ = suc})
                                      | rename-* (ext suc) M
                                      | rename-* suc N
                                      = refl


exts-ts-commute : ∀ {n m} {σ : Subst n m}
  → exts (σ *ˢ) ≡ (exts σ) *ˢ
exts-ts-commute {n}{m}{σ} = extensionality exts-ts-commute′
  where
    exts-ts-commute′ : (x : Fin (suc n))
      → (exts (σ *ˢ)) x ≡ ((exts σ) *ˢ) x
    exts-ts-commute′ zero    = refl
    exts-ts-commute′ (suc x) = rename-suc-ts σ x


subst-ts : ∀ {n m} (σ : Subst n m) (M : Term n)
  → subst (σ *ˢ) (M *) —↠ (subst σ M) *
subst-ts σ (# x) = σ x * ∎
subst-ts σ (ƛ M) rewrite exts-ts-commute {σ = σ} = —↠-cong-ƛ (subst-ts (exts σ) M)
subst-ts σ (# x · N) = —↠-trans (—↠-cong (subst-ts σ (# x)) (subst-ts σ N))
                                (app-*-join (σ x) (subst σ N))
subst-ts σ (M₁ · M₂ · N) = —↠-cong (subst-ts σ (M₁ · M₂)) (subst-ts σ N)
subst-ts σ ((ƛ M) · N) rewrite sym (subst-commute {N = M *}{M = N *}{σ = σ *ˢ})
                             | exts-ts-commute {σ = σ}
                             = sub-betas (subst-ts (exts σ) M) (subst-ts σ N)


subst-zero-ts : ∀ {n} {N : Term n}
  → subst-zero (N *) ≡ (subst-zero N) *ˢ
subst-zero-ts = extensionality (λ { zero → refl ; (suc r) → refl })


lemma3-4 : ∀ {n} (M : Term (suc n)) (N : Term n)
  → M * [ N * ] —↠ (M [ N ]) *
lemma3-4 M N rewrite subst-zero-ts {N = N} = subst-ts (subst-zero N) M


lemma3-5 : ∀ {n} {M N : Term n}
  → M   —→ N
    ----------
  → M * —↠ N *
lemma3-5 {M = # x} M—→N = # x —→⟨ M—→N ⟩ lemma3-2
lemma3-5 {M = ƛ M}         (—→-ƛ  M—→M′)  = —↠-cong-ƛ (lemma3-5 M—→M′)
lemma3-5 {M = # _     · N} (—→-ξᵣ M₂—→M′) = —↠-congᵣ  (lemma3-5 M₂—→M′)
lemma3-5 {M = (ƛ M)   · N}  —→-β                 = lemma3-4 M N
lemma3-5 {M = (ƛ M)   · N} (—→-ξₗ (—→-ƛ M—→M′)) = sub-betas (lemma3-5 M—→M′) (N * ∎)
lemma3-5 {M = (ƛ M)   · N} (—→-ξᵣ N—→N′)        = sub-betas (M * ∎) (lemma3-5 N—→N′)
lemma3-5 {M = M₁ · M₂ · _} (—→-ξᵣ N—→N′)                         = —↠-congᵣ (lemma3-5 N—→N′)
lemma3-5 {M = M₁ · M₂ · _} (—→-ξₗ {M′ = # x}       M₁M₂—→#x)     = —↠-congₗ (lemma3-5 M₁M₂—→#x)
lemma3-5 {M = M₁ · M₂ · _} (—→-ξₗ {M′ = M′₁ · M′₂} M₁M₂—→M′₁M′₂) = —↠-congₗ (lemma3-5 M₁M₂—→M′₁M′₂)
lemma3-5 {M = M₁ · M₂ · K} (—→-ξₗ {M′ = ƛ M′}      M₁M₂—→ƛM′)    =
  —↠-trans (—↠-congₗ (lemma3-5 M₁M₂—→ƛM′))
           ((ƛ M′ *) · K * —→⟨ —→-β ⟩ subst (subst-zero (K *)) (M′ *) ∎)


corollary3-6 : ∀ {n} {M N : Term n}
  → M   —↠ N
    ----------
  → M * —↠ N *
corollary3-6 (M ∎) = M * ∎
corollary3-6 (M —→⟨ M—→L ⟩ L—↠N) = —↠-trans (lemma3-5 M—→L) (corollary3-6 L—↠N)


corollary3-7 : ∀ {n} {M N : Term n} (m : ℕ)
  → M        —↠ N
    --------------------
  → M *⁽ m ⁾ —↠ N *⁽ m ⁾
corollary3-7 zero    M—↠N = M—↠N
corollary3-7 (suc m) M—↠N = corollary3-7 m (corollary3-6 M—↠N)


theorem3-8 : ∀ {n} {M N : Term n} {m : ℕ}
  → M —↠⁽ m ⁾ N
    -------------
  → N —↠ M *⁽ m ⁾
theorem3-8 {m = zero}  (M ∎) = M ∎
theorem3-8 {m = suc m} (M —→⁽⁾⟨ M—→L ⟩ L—↠ᵐN) =
  —↠-trans (theorem3-8 L—↠ᵐN) (corollary3-7 m (lemma3-3 M—→L))


unnamed-named : ∀ {n} {M N : Term n}
  →         M —↠      N
    --------------------
  → ∃[ k ] (M —↠⁽ k ⁾ N)
unnamed-named (M ∎) = zero , (M ∎)
unnamed-named (M —→⟨ M—→L ⟩ L—↠N) with unnamed-named L—↠N
... | k′ , L—↠ᵏ′N = suc k′ , (M —→⁽⁾⟨ M—→L ⟩ L—↠ᵏ′N)

lift-* : ∀ {n} (M : Term n) (k : ℕ)
  → M —↠ M *⁽ k ⁾
lift-* M zero    = M ∎
lift-* M (suc k) = —↠-trans lemma3-2 (lift-* (M *) k)

complete-* : ∀ {k} (M : Term k) {n m : ℕ}
  → n ≤ m
    --------------------
  → M *⁽ n ⁾ —↠ M *⁽ m ⁾
complete-* M {m = m} z≤n = lift-* M m
complete-* M (s≤s k) = complete-* (M *) k

theorem3-9 : ∀ {n} {M A B : Term n}
  →          M —↠ A  →  M —↠ B
    ----------------------------
  → ∃[ N ] ((A —↠ N) × (B —↠ N))
theorem3-9 {M = M} M—↠A M—↠B =
    let n , M—↠ⁿA = unnamed-named M—↠A
        m , M—↠ᵐB = unnamed-named M—↠B
        A—↠M*ⁿ = theorem3-8 M—↠ⁿA
        B—↠M*ᵐ = theorem3-8 M—↠ᵐB
     in [ (λ n≤m →
            let M*ⁿ—↠M*ᵐ : M *⁽ n ⁾ —↠ M *⁽ m ⁾
                M*ⁿ—↠M*ᵐ = complete-* M n≤m
             in M *⁽ m ⁾ , —↠-trans A—↠M*ⁿ M*ⁿ—↠M*ᵐ , B—↠M*ᵐ)
        , (λ m≤n →
            let M*ᵐ—↠M*ⁿ : M *⁽ m ⁾ —↠ M *⁽ n ⁾
                M*ᵐ—↠M*ⁿ = complete-* M m≤n
             in M *⁽ n ⁾ , A—↠M*ⁿ , —↠-trans B—↠M*ᵐ M*ᵐ—↠M*ⁿ)
        ] (≤-total n m)
