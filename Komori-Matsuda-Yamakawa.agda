open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; sym; cong₂)
open import Data.Nat
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

  begin : ∀ {n} (M : Term n)
      --------
    → M —↠₍ zero ₎ M

  _—→₍₎⟨_⟩_ : ∀ {k} {n} {M N : Term n} (L : Term n)
    → L —→ M
    → M —↠₍ k ₎ N
      ---------
    → L —↠₍ suc k ₎ N


betas-subst : ∀{n m} → Subst n m → Subst n m → Set
betas-subst {n}{m} σ σ′ = ∀{x : Fin n} → σ x —↠ σ′ x

beta-subst : ∀{n m} → Subst n m → Subst n m → Set
beta-subst {n}{m} σ σ′ = ∀{x : Fin n} → σ x —→ σ′ x

beta-rename : ∀{n m} {ρ : Rename n m} {M M′ : Term n}
    → M —→ M′
      -------------------------
    → rename ρ M —→ rename ρ M′
beta-rename (—→-ξ₁ x) = —→-ξ₁ (beta-rename x)
beta-rename (—→-ξ₂ x) = —→-ξ₂ (beta-rename x)
beta-rename {ρ = ρ}(—→-β{N = N}{M = M}) rewrite sym (rename-subst-commute{N = N}{M = M}{ρ = ρ}) = —→-β
beta-rename (—→-ƛ x) = —→-ƛ (beta-rename x)

betas-rename : ∀{n m} {ρ : Rename n m} {M M′ : Term n}
    → M —↠ M′
      -------------------------
    → rename ρ M —↠ rename ρ M′
betas-rename {ρ = ρ} (M ∎) = rename ρ M ∎
betas-rename {ρ = ρ} (L —→⟨ x ⟩ x₁) = rename ρ L —→⟨ beta-rename x ⟩ betas-rename x₁

betas-subst-ext : ∀{n m}{σ τ : Subst n m}
    → betas-subst σ        τ
      -----------------------------
    → betas-subst (exts σ) (exts τ)
betas-subst-ext s {zero}  = # zero ∎
betas-subst-ext s {suc x} = betas-rename s

base : ∀{n m}{M : Term n}{σ τ : Subst n m}
    → betas-subst σ τ
      ----------------------
    → subst σ M —↠ subst τ M
base {M = # x} s = s
base {n}{m}{M = ƛ M}{σ}{τ} s = abs-cong (base{M = M} (λ {x} → betas-subst-ext s {x = x}))
base {M = N · M} s = —↠-trans (appL-cong (base{M = N} s)) (appR-cong (base{M = M} s))

base-ext : ∀{n m}{M M′ : Term n}{σ : Subst n m}
    → M —→ M′
      -----------------------
    → subst σ M —→ subst σ M′
base-ext (—→-ξ₁ x) = —→-ξ₁ (base-ext x)
base-ext (—→-ξ₂ x) = —→-ξ₂ (base-ext x)
base-ext {σ = σ}(—→-β{N = N}{M = M}) rewrite sym (subst-commute{N = N}{M = M}{σ = σ}) = —→-β
base-ext (—→-ƛ x) = —→-ƛ (base-ext x)

subst-betas : ∀{n m} {σ τ : Subst n m} {M M′ : Term n}
    → betas-subst σ τ
    → M —↠ M′
      ----------------------
    → subst σ M —↠ subst τ M′
subst-betas s (M ∎) = base{M = M} s
subst-betas{σ = σ}{τ} s (L —→⟨ x ⟩ k) = subst σ L —→⟨ base-ext x ⟩ subst-betas s k

betas-subst-zero : ∀ {n} {M M′ : Term n}
    → M —↠ M′
      ------------------------------------------
    → betas-subst (subst-zero M) (subst-zero M′)
betas-subst-zero {M} {M′} p {zero} = p
betas-subst-zero {M} {M′} p {suc a} = # a ∎

sub-betas : ∀{n}{M M′ : Term (suc n)}{N N′ : Term n}
    → M —↠ M′
    → N —↠ N′
      --------------------
    → M [ N ] —↠ M′ [ N′ ]
sub-betas bm bn = subst-betas (betas-subst-zero bn) bm

lemma3-2 : ∀{n} {M : Term n}
    → M —↠ M *
lemma3-2 {n} {# x} = # x ∎
lemma3-2 {n} {ƛ M} = abs-cong lemma3-2 
lemma3-2 {n} {# x · N} = appR-cong lemma3-2
lemma3-2 {n} {(ƛ M) · N} = (ƛ M) · N —→⟨ —→-β ⟩ (sub-betas {M = M} lemma3-2 lemma3-2)
lemma3-2 {n} {L · M · N} =
    —↠-trans (appL-cong lemma3-2)
             (appR-cong lemma3-2)

beta-complete : ∀ {n} {N N′ : Term (suc n)} {M M′ : Term n}
    → N —↠ N′
    → M —↠ M′
    ------------------------
    → (ƛ N) · M —↠ N′ [ M′ ]
beta-complete {N = N} {M = M} a b = (ƛ N) · M —→⟨ —→-β ⟩ (sub-betas a b)

lemma3-3 : ∀{n} {M N : Term n}
    → M —→ N
      --------
    → N —↠ M *
lemma3-3 {M = # _} ()
lemma3-3 {M = ƛ M} (—→-ƛ M—→N) = abs-cong (lemma3-3 M—→N)
lemma3-3 {M = # _ · _} (—→-ξ₂ x) = appR-cong (lemma3-3 x)
lemma3-3 {M = (ƛ M) · N} (—→-ξ₂ x)        = beta-complete  lemma3-2   (lemma3-3 x)
lemma3-3 {M = (ƛ M) · N} (—→-ξ₁ (—→-ƛ x)) = beta-complete (lemma3-3 x) lemma3-2
lemma3-3 {M = _ · _ · _} (—→-ξ₂ ll') = —↠-trans (appL-cong lemma3-2) (appR-cong (lemma3-3 ll'))
lemma3-3 {M = _ · _ · _} (—→-ξ₁ ll') = —↠-trans (appR-cong lemma3-2) (appL-cong (lemma3-3 ll'))
lemma3-3 {M = (ƛ M) · N} —→-β = sub-betas {M = M} lemma3-2 lemma3-2

hard : ∀{n} (u : Term n) {s : Term n}
   → u * · s * —↠ (u · s) *
hard {n}(# x  ){s} = # x · s * ∎
hard {n}(ƛ u  ){s} = (ƛ u *) · s * —→⟨ —→-β ⟩ subst (subst-zero (s *)) (u *) ∎
hard {n}(N · M){s} = (N · M) * · s * ∎

ts : ∀{n m} (σ : Subst n m) → Subst n m
ts σ = λ x → (σ x) *

fundamental : ∀{n m} (ρ : Rename n m) (N : Term n)
   → rename ρ (N *) ≡ rename ρ N *
fundamental ρ (# x) = refl
fundamental ρ (ƛ N) rewrite fundamental (ext ρ) N = refl
fundamental ρ (# x · N) rewrite fundamental ρ N = refl
fundamental ρ (N₁ · N₂ · M) = cong₂ _·_ (fundamental ρ (N₁ · N₂)) (fundamental ρ M) 
fundamental ρ ((ƛ N) · M) rewrite sym (rename-subst-commute{N = N *}{M = M *}{ρ})
                                | fundamental (ext ρ) N
                                | fundamental ρ M
                                = refl 

ts-rename : ∀{n m} (σ : Subst n m) (r : Fin n)
   → rename suc (ts σ r) ≡ ts (exts σ) (suc r)
ts-rename σ r with σ r 
ts-rename σ r | # x = refl
ts-rename σ r | ƛ N rewrite fundamental (ext suc) N = refl
ts-rename σ r | (ƛ N) · M rewrite sym (rename-subst-commute{N = N *}{M = M *}{ρ = suc})
                                | fundamental (ext suc) N
                                | fundamental suc M = refl
ts-rename σ r | # x · M rewrite fundamental suc M = refl
ts-rename σ r | N₁ · N₂ · M = cong₂ _·_ (fundamental suc (N₁ · N₂)) (fundamental suc M)

-- subst (subst-zero (rename ρ M *))   (rename (ext ρ) N *)   ≡ exts σ (ρ r) *
-- subst (subst-zero (rename ρ M *))   (rename (ext ρ) (N *)) ≡ exts σ (ρ r) *
-- subst (subst-zero (rename ρ (M *))) (rename (ext ρ) (N *)) ≡ exts σ (ρ r) *
-- rename ρ (subst (subst-zero (N *)) (M *)) ≡ exts σ (ρ r) *
-- rename ρ ((M *) [ N * ]) ≡ exts σ (ρ r) *

ts-ext-commute : ∀{n m} {σ : Subst n m}
    → exts (ts σ) ≡ ts (exts σ)
ts-ext-commute{n}{m}{σ} = extensionality ts-ext-commute′
   where
     ts-ext-commute′ : (r : Fin (suc n))
       → exts (ts σ) r ≡ ts (exts σ) r
     ts-ext-commute′ zero = refl
     ts-ext-commute′ (suc r) = ts-rename σ r

lemma-gen : ∀{n m} (σ : Subst n m) (t : Term n)
    → subst (ts σ) (t *) —↠ (subst σ t) *
lemma-gen σ (# x) = σ x * ∎
lemma-gen σ (ƛ t) rewrite ts-ext-commute{σ = σ} = abs-cong (lemma-gen (exts σ) t)
lemma-gen σ (# x · M) = —↠-trans (—↠-trans (appL-cong (lemma-gen σ (# x)))
                                            (appR-cong (lemma-gen σ M)))
                                 (hard (σ x))
lemma-gen σ (N₁ · N₂ · M) = —↠-trans (appL-cong (lemma-gen σ (N₁ · N₂)))
                                     (appR-cong (lemma-gen σ M))
lemma-gen σ ((ƛ N) · M) rewrite sym (subst-commute{N = N *}{M = M *}{σ = ts σ})
                              | ts-ext-commute {σ = σ} =
    sub-betas (lemma-gen (exts σ) N) (lemma-gen σ M)

lemma-conversione : ∀{n}{s : Term n} → subst-zero (s *) ≡ ts (subst-zero s)
lemma-conversione = extensionality (λ{ Data.Fin.0F → refl ; (suc r) → refl })

lemma3-4 : ∀{n} (t : Term (suc n)) (s : Term n)
    → t * [ s * ] —↠ (t [ s ]) *
lemma3-4 t s rewrite lemma-conversione{s = s} = lemma-gen (subst-zero s) t

lemma-abs-apply : ∀{n}{L′ : Term (suc n)}{B : Term n}
    → (ƛ L′ *) · B * —↠ (L′ *) [ B * ]
lemma-abs-apply {L′ = L′}{B = B} = beta-complete (L′ * ∎) (B * ∎)

lemma3-5 : ∀{n} {M N : Term n}
    → M   —→ N
    ------------
    → M * —↠ N *
lemma3-5 {M = # x} M—→N = # x —→⟨ M—→N ⟩ lemma3-2
lemma3-5 {M = ƛ M} (—→-ƛ M—→N)       = abs-cong  (lemma3-5 M—→N)
lemma3-5 {M = # x · M₁} (—→-ξ₂ M—→N) = appR-cong (lemma3-5 M—→N)
lemma3-5 {M = (ƛ P₁) · P₂} —→-β      = lemma3-4 P₁ P₂
lemma3-5 {M = (ƛ P₁) · P₂} (—→-ξ₁ (—→-ƛ x)) = sub-betas (lemma3-5 x) (P₂ * ∎)
lemma3-5 {M = (ƛ P₁) · P₂} (—→-ξ₂ x)        = sub-betas (P₁ * ∎) (lemma3-5 x)
lemma3-5 {M = # x · B}    {.(_ · B)} (—→-ξ₁ ())
lemma3-5 {M = M · A₁ · B} {.(# x · B)} (—→-ξ₁ {L′ = # x} k)           = appL-cong (lemma3-5 k)
lemma3-5 {M = M · A₁ · B} {.(L′ · L′₁ · B)} (—→-ξ₁ {L′ = L′ · L′₁} k) = appL-cong (lemma3-5 k)
lemma3-5 {M = M · A₁ · B} {.(M · A₁ · _)} (—→-ξ₂ k)                   = appR-cong (lemma3-5 k)
lemma3-5 {M = M · A₁ · B} {.((ƛ L′) · B)} (—→-ξ₁ {L′ = ƛ L′} k)       = —↠-trans (appL-cong{M = B *} (lemma3-5 k))
                                                                                 (lemma-abs-apply{L′ = L′}{B = B})

corollary3-6 : ∀{n} {M N : Term n}
    → M   —↠ N
    ------------
    → M * —↠ N *
corollary3-6 (M ∎) = M * ∎
corollary3-6 (_ —→⟨ r ⟩ M—↠N) = —↠-trans (lemma3-5 r) (corollary3-6 M—↠N)

corollary3-7 : ∀{n} {m} {M N : Term n}
    → M        —↠ N
    ----------------------
    → M *₍ m ₎ —↠ N *₍ m ₎
corollary3-7 {m = zero} x = x
corollary3-7 {m = suc m} x = corollary3-7 {m = m} (corollary3-6 x)

theorem3-8 : ∀{n} {m} {M N : Term n}
    → M —↠₍ m ₎ N
    --------------
    → N —↠ M *₍ m ₎
theorem3-8 {m = zero} (begin M) = M ∎
theorem3-8 {m = suc m} (L —→₍₎⟨ x ⟩ RN) =
    —↠-trans (theorem3-8 RN) (corollary3-7 {m = m} (lemma3-3 x))

unnamed-named : ∀{n} {A B : Term n}
    →         A —↠      B
      --------------------
    → ∃[ m ] (A —↠₍ m ₎ B)
unnamed-named (M ∎) = zero , begin M
unnamed-named (L —→⟨ x ⟩ LA) with unnamed-named LA
... | m′ , ab = suc m′ , (L —→₍₎⟨ x ⟩ ab)

triangle : ∀{k} {m n} {M : Term k}
   → m ≤ n
     --------------------
   → M *₍ m ₎ —↠ M *₍ n ₎
triangle {n = suc n} z≤n = —↠-trans lemma3-2 (triangle {n = n} z≤n)
triangle {n = zero} {M = M} z≤n = M ∎
triangle {n = suc n} (s≤s a) = triangle a

theorem3-9 : ∀{n} {M M₁ M₂ : Term n}
             → M  —↠ M₁ →  M  —↠ M₂
      ------------------------------
    → ∃[ N ] ((M₁ —↠ N) × (M₂ —↠ N))
theorem3-9 {n}{M} MM₁ MM₂ = 
    let n , MₙM₁ = unnamed-named MM₁
        m , MₘM₂ = unnamed-named MM₂
        M₁Mⁿ* = theorem3-8 MₙM₁
        M₂Mᵐ* = theorem3-8 MₘM₂
     in [ (λ n≤m →
            let Mⁿ*Mᵐ* : M *₍ n ₎ —↠ M *₍ m ₎
                Mⁿ*Mᵐ* = triangle{m = n}{n = m} n≤m
             in M *₍ m ₎ , —↠-trans M₁Mⁿ* Mⁿ*Mᵐ* , M₂Mᵐ*)
        , (λ m≤n →
            let Mᵐ*Mⁿ* : M *₍ m ₎ —↠ M *₍ n ₎
                Mᵐ*Mⁿ* = triangle m≤n
             in M *₍ n ₎ , M₁Mⁿ* , —↠-trans M₂Mᵐ* Mᵐ*Mⁿ*)
        ] (≤-total n m)
        
