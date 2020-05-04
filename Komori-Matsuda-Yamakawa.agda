open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym; cong; cong₂)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-total)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum
open import Data.Product using (∃; _×_; _,_; ∃-syntax)
open import DeBruijn
open import Substitution
open import Beta
open import ChurchRosser
open import Parallel

infix 5 _*₍_₎

_*₍_₎ : ∀{n} → Term n → ℕ → Term n
M *₍ zero ₎  = M
M *₍ suc n ₎ = (M *) *₍ n ₎

data _—↠₍_₎_ : ∀ {n} → Term n → ℕ → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      --------------
    → M —↠₍ zero ₎ M

  _—→₍₎⟨_⟩_ : ∀ {k} {n} {L N : Term n} (M : Term n)
    → M —→ L
    → L —↠₍ k ₎ N
      ---------------
    → M —↠₍ suc k ₎ N


lemma3-2 : ∀ {n} {M : Term n}
  → M —↠ M *
lemma3-2 {M = # x}       = # x ∎
lemma3-2 {M = ƛ _}       = —↠-ƛ-cong lemma3-2
lemma3-2 {M = # _ · _}   = —↠-congᵣ  lemma3-2
lemma3-2 {M = _ · _ · _} = —↠-cong   lemma3-2 lemma3-2
lemma3-2 {M = (ƛ M) · N} = (ƛ M) · N —→⟨ —→-β ⟩ (sub-betas {M = M} lemma3-2 lemma3-2)


lemma3-3 : ∀ {n} {M N : Term n}
  → M —→ N
    --------
  → N —↠ M *
lemma3-3 {M = # _} ()
lemma3-3 {M = ƛ M}         (—→-ƛ M—→N)          = —↠-ƛ-cong (lemma3-3 M—→N)
lemma3-3 {M = # _ · M}     (—→-ξᵣ M—→M′)        = —↠-congᵣ  (lemma3-3 M—→M′)
lemma3-3 {M = _ · _   · M} (—→-ξᵣ M—→M′)        = —↠-cong  lemma3-2          (lemma3-3 M—→M′)
lemma3-3 {M = M₁ · M₂ · _} (—→-ξₗ M₁M₂—↠M′)     = —↠-cong (lemma3-3 M₁M₂—↠M′) lemma3-2
lemma3-3 {M = (ƛ M) · N}   (—→-ξᵣ N—→M′)        = beta-complete  lemma3-2       (lemma3-3 N—→M′)
lemma3-3 {M = (ƛ M) · N}   (—→-ξₗ (—→-ƛ M—→N′)) = beta-complete (lemma3-3 M—→N′) lemma3-2
lemma3-3 {M = (ƛ M) · N}   —→-β                 = sub-betas {M = M} lemma3-2 lemma3-2


app-*-join : ∀ {n} (M : Term n) {N : Term n}
  → M * · N * —↠ (M · N) *
app-*-join (# x)     {N} = # x · N * ∎
app-*-join (ƛ M)     {N} = (ƛ M *) · N * —→⟨ —→-β ⟩ subst (subst-zero (N *)) (M *) ∎
app-*-join (M₁ · M₂) {N} = (M₁ · M₂) * · N * ∎


rename-* : ∀ {n m} (ρ : Rename n m) (M : Term n)
  → rename ρ (M *) ≡ (rename ρ M) *
rename-* ρ (# _)         = refl
rename-* ρ (ƛ M)         = cong ƛ_ (rename-* (ext ρ) M)
rename-* ρ (# _ · N)     = cong₂ _·_ refl                   (rename-* ρ N)
rename-* ρ (M₁ · M₂ · N) = cong₂ _·_ (rename-* ρ (M₁ · M₂)) (rename-* ρ N)
rename-* ρ ((ƛ N) · M) rewrite sym (rename-subst-commute {N = N *}{M = M *}{ρ = ρ})
                             | rename-* (ext ρ) N
                             | rename-* ρ M
                             = refl


ts : ∀ {n m} (σ : Subst n m) → Subst n m
ts σ = λ x → (σ x) *


rename-ts : ∀ {n m} (σ : Subst n m) (x : Fin n)
  → rename suc (ts σ x) ≡ ts (exts σ) (suc x)
rename-ts σ x with σ x
rename-ts σ x | # _         = refl
rename-ts σ x | ƛ M         = cong ƛ_ (rename-* (ext suc) M)
rename-ts σ x | # _ · N     = cong₂ _·_ refl                     (rename-* suc N)
rename-ts σ x | M₁ · M₂ · N = cong₂ _·_ (rename-* suc (M₁ · M₂)) (rename-* suc N)
rename-ts σ x | (ƛ N) · M rewrite sym (rename-subst-commute {N = N *}{M = M *}{ρ = suc})
                                | rename-* (ext suc) N
                                | rename-* suc M
                                = refl


exts-ts-commute : ∀ {n m} {σ : Subst n m}
  → exts (ts σ) ≡ ts (exts σ)
exts-ts-commute {n}{m}{σ} = extensionality exts-ts-commute′
  where
    exts-ts-commute′ : (x : Fin (suc n))
      → exts (ts σ) x ≡ ts (exts σ) x
    exts-ts-commute′ zero    = refl
    exts-ts-commute′ (suc x) = rename-ts σ x


subst-ts : ∀ {n m} (σ : Subst n m) (M : Term n)
  → subst (ts σ) (M *) —↠ (subst σ M) *
subst-ts σ (# x) = σ x * ∎
subst-ts σ (ƛ M) rewrite exts-ts-commute {σ = σ} = —↠-ƛ-cong (subst-ts (exts σ) M)
subst-ts σ (# x · N) = —↠-trans (—↠-cong (subst-ts σ (# x)) (subst-ts σ N))
                                (app-*-join (σ x))
subst-ts σ (M₁ · M₂ · N) = —↠-cong (subst-ts σ (M₁ · M₂)) (subst-ts σ N)
subst-ts σ ((ƛ N) · M) rewrite sym (subst-commute {N = N *}{M = M *}{σ = ts σ})
                             | exts-ts-commute {σ = σ}
                             = sub-betas (subst-ts (exts σ) N) (subst-ts σ M)


subst-zero-ts-commute : ∀ {n} {N : Term n}
  → subst-zero (N *) ≡ ts (subst-zero N)
subst-zero-ts-commute = extensionality (λ{ zero → refl ; (suc r) → refl })


lemma3-4 : ∀ {n} (M : Term (suc n)) (N : Term n)
  → M * [ N * ] —↠ (M [ N ]) *
lemma3-4 M N rewrite subst-zero-ts-commute {N = N} = subst-ts (subst-zero N) M


lemma3-5 : ∀ {n} {M N : Term n}
  → M   —→ N
    ----------
  → M * —↠ N *
lemma3-5 {M = # x} M—→N = # x —→⟨ M—→N ⟩ lemma3-2
lemma3-5 {M = ƛ _}     (—→-ƛ  M—→N)   = —↠-ƛ-cong (lemma3-5 M—→N)
lemma3-5 {M = # _ · _} (—→-ξᵣ M₂—→M′) = —↠-congᵣ (lemma3-5 M₂—→M′)
lemma3-5 {M = (ƛ M₁) · M₂} —→-β                  = lemma3-4 M₁ M₂
lemma3-5 {M = (ƛ M₁) · M₂} (—→-ξₗ (—→-ƛ M₁—→N′)) = sub-betas (lemma3-5 M₁—→N′) (M₂ * ∎)
lemma3-5 {M = (ƛ M₁) · M₂} (—→-ξᵣ M₂—→M′)        = sub-betas (M₁ * ∎) (lemma3-5 M₂—→M′)
lemma3-5 {M = M₁ · M₂ · _} (—→-ξᵣ K—→M′)                     = —↠-congᵣ (lemma3-5 K—→M′)
lemma3-5 {M = M₁ · M₂ · _} (—→-ξₗ {M′ = # x}     M₁M₂—→#x)   = —↠-congₗ (lemma3-5 M₁M₂—→#x)
lemma3-5 {M = M₁ · M₂ · _} (—→-ξₗ {M′ = N₁ · N₂} M₁M₂—→N₁N₂) = —↠-congₗ (lemma3-5 M₁M₂—→N₁N₂)
lemma3-5 {M = M₁ · M₂ · K} (—→-ξₗ {M′ = ƛ N₁} M₁M₂—→ƛN₁)     =
  —↠-trans (—↠-congₗ (lemma3-5 M₁M₂—→ƛN₁))
           ((ƛ N₁ *) · K * —→⟨ —→-β ⟩ subst (subst-zero (K *)) (N₁ *) ∎)

corollary3-6 : ∀ {n} {M N : Term n}
  → M   —↠ N
    ----------
  → M * —↠ N *
corollary3-6 (M ∎) = M * ∎
corollary3-6 (_ —→⟨ r ⟩ M—↠N) = —↠-trans (lemma3-5 r) (corollary3-6 M—↠N)


corollary3-7 : ∀ {n} {M N : Term n} (m : ℕ)
  → M        —↠ N
    --------------------
  → M *₍ m ₎ —↠ N *₍ m ₎
corollary3-7 zero    M—↠N = M—↠N
corollary3-7 (suc m) M—↠N = corollary3-7 m (corollary3-6 M—↠N)


theorem3-8 : ∀ {n} {M N : Term n} {m : ℕ}
  → M —↠₍ m ₎ N
    -------------
  → N —↠ M *₍ m ₎
theorem3-8 {m = zero}  (M ∎) = M ∎
theorem3-8 {m = suc m} (L —→₍₎⟨ L—→M ⟩ M—↠ₘN) =
  —↠-trans (theorem3-8 M—↠ₘN) (corollary3-7 m (lemma3-3 L—→M))


unnamed-named : ∀ {n} {M N : Term n}
  →         M —↠      N
    --------------------
  → ∃[ m ] (M —↠₍ m ₎ N)
unnamed-named (M ∎) = zero , (M ∎)
unnamed-named (L —→⟨ L—→M ⟩ M—↠N) with unnamed-named M—↠N
... | m′ , M—↠ₘ′N = suc m′ , (L —→₍₎⟨ L—→M ⟩ M—↠ₘ′N)


triangle : ∀ {k} {m n : ℕ} {M : Term k}
  → m ≤ n
    --------------------
  → M *₍ m ₎ —↠ M *₍ n ₎
triangle {n = zero}{M = M} z≤n = M ∎
triangle {n = suc n} z≤n = —↠-trans lemma3-2 (triangle {n = n} z≤n)
triangle {n = suc n} (s≤s k) = triangle k


theorem3-9 : ∀ {n} {M M₁ M₂ : Term n}
  →          M  —↠ M₁ →  M  —↠ M₂
    ------------------------------
  → ∃[ N ] ((M₁ —↠ N) × (M₂ —↠ N))
theorem3-9 {n}{M} M—↠M₁ M—↠M₂ =
    let n , Mₙ—↠M₁ = unnamed-named M—↠M₁
        m , Mₘ—↠M₂ = unnamed-named M—↠M₂
        M₁—↠Mⁿ* = theorem3-8 Mₙ—↠M₁
        M₂—↠Mᵐ* = theorem3-8 Mₘ—↠M₂
     in [ (λ n≤m →
            let Mⁿ*—↠Mᵐ* : M *₍ n ₎ —↠ M *₍ m ₎
                Mⁿ*—↠Mᵐ* = triangle n≤m
             in M *₍ m ₎ , —↠-trans M₁—↠Mⁿ* Mⁿ*—↠Mᵐ* , M₂—↠Mᵐ*)
        , (λ m≤n →
            let Mᵐ*—↠Mⁿ* : M *₍ m ₎ —↠ M *₍ n ₎
                Mᵐ*—↠Mⁿ* = triangle m≤n
             in M *₍ n ₎ , M₁—↠Mⁿ* , —↠-trans M₂—↠Mᵐ* Mᵐ*—↠Mⁿ*)
        ] (≤-total n m)
