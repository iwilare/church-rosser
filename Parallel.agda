import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst₂; cong)
open import Data.Nat.Base
open import Data.Fin hiding (_+_; #_)
open import Data.Product using (∃; _×_; _,_; ∃-syntax)
open import DeBruijn
open import Substitution
open import Beta

infix 4 _⇉_

data _⇉_ : ∀ {n} → Term n → Term n → Set where

  ⇉-c : ∀ {n} {x : Fin n}
      ---------
    → # x ⇉ # x

  ⇉-ƛ : ∀ {n} {M M′ : Term (suc n)}
    → M ⇉ M′
      ----------
    → ƛ M ⇉ ƛ M′

  ⇉-ξ : ∀ {n} {M M′ N N′ : Term n}
    → M ⇉ M′
    → N ⇉ N′
      ---------------
    → M · N ⇉ M′ · N′

  ⇉-β : ∀ {n} {M M′ : Term (suc n)} {N N′ : Term n}
    → M ⇉ M′
    → N ⇉ N′
      ---------------------
    → (ƛ M) · N ⇉ M′ [ N′ ]


par-subst : ∀{n m} → Subst n m → Subst n m → Set
par-subst σ σ′ = ∀ {x} → σ x ⇉ σ′ x


par-rename : ∀{n m} {ρ : Rename n m} {M M′ : Term n}
  → M ⇉ M′
    ------------------------
  → rename ρ M ⇉ rename ρ M′
par-rename ⇉-c         = ⇉-c
par-rename (⇉-ƛ p)     = ⇉-ƛ (par-rename p)
par-rename (⇉-ξ p₁ p₂) = ⇉-ξ (par-rename p₁) (par-rename p₂)
par-rename {n}{m}{ρ} (⇉-β {n}{N}{N′}{M}{M′} p₁ p₂)
    with ⇉-β (par-rename {ρ = ext ρ} p₁) (par-rename {ρ = ρ} p₂)
... | G rewrite rename-subst-commute {n}{m}{N′}{M′}{ρ} = G


par-subst-exts : ∀{n m} {σ σ′ : Subst n m}
  → par-subst σ σ′
    ---------------------------
  → par-subst (exts σ) (exts σ′)
par-subst-exts s {x = zero} = ⇉-c
par-subst-exts s {x = suc x} = par-rename s


subst-par : ∀{n m} {σ σ′ : Subst n m} {M M′ : Term n}
  → par-subst σ σ′
  → M ⇉ M′
    ----------------------
  → subst σ M ⇉ subst σ′ M′
subst-par {M = # x} s ⇉-c = s
subst-par {n}{m}{σ}{σ′} {ƛ N} s (⇉-ƛ p) =
  ⇉-ƛ (subst-par {σ = exts σ}{σ′ = exts σ′}
         (λ {x} → par-subst-exts s {x = x}) p)
subst-par {M = L · M} s (⇉-ξ p₁ p₂) =
  ⇉-ξ (subst-par s p₁) (subst-par s p₂)
subst-par {n}{m}{σ}{σ′} {(ƛ N) · M} s (⇉-β {M′ = M′}{N′ = N′} p₁ p₂)
    with ⇉-β (subst-par {σ = exts σ}{σ′ = exts σ′}{M = N}
                        (λ {x} → par-subst-exts s {x = x}) p₁)
             (subst-par {σ = σ} s p₂)
... | G rewrite subst-commute {N = M′}{M = N′}{σ = σ′} = G


par-subst-zero : ∀ {n} {M M′ : Term n}
  → M ⇉ M′
    ----------------------------------------
  → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero M⇉M′ {zero} = M⇉M′
par-subst-zero M⇉M′ {suc x} = ⇉-c


sub-par : ∀{n} {M M′ : Term (suc n)} {N N′ : Term n}
  → M ⇉ M′
  → N ⇉ N′
    -------------------
  → M [ N ] ⇉ M′ [ N′ ]
sub-par M⇉M′ N⇉N′ = subst-par (par-subst-zero N⇉N′) M⇉M′


par-refl : ∀ {n} {M : Term n}
    -----
  → M ⇉ M
par-refl {M = # x}   = ⇉-c
par-refl {M = ƛ N}   = ⇉-ƛ par-refl
par-refl {M = L · M} = ⇉-ξ par-refl par-refl


beta-par : ∀{n} {M N : Term n}
  → M —→ N
    ------
  → M ⇉ N
beta-par {M = L · M} (—→-ξₗ r) = ⇉-ξ (beta-par {M = L} r) par-refl
beta-par {M = L · M} (—→-ξᵣ r) = ⇉-ξ par-refl (beta-par {M = M} r)
beta-par {M = ƛ N} (—→-ƛ r) = ⇉-ƛ (beta-par r)
beta-par {M = (ƛ N) · M} —→-β = ⇉-β par-refl par-refl


par-betas : ∀ {n} {M N : Term n}
  → M ⇉ N
    ------
  → M —↠ N
par-betas {M = # _} (⇉-c {x = x}) = # x ∎
par-betas {M = ƛ M} (⇉-ƛ p) = —↠-cong-ƛ (par-betas p)
par-betas {M = M · N} (⇉-ξ p₁ p₂) = —↠-cong (par-betas p₁) (par-betas p₂)
par-betas {M = (ƛ M) · N} (⇉-β {M′ = M′}{N′ = N′} p₁ p₂) =
  let a : (ƛ M) · N —↠ (ƛ M′) · N
      a = —↠-congₗ (—↠-cong-ƛ (par-betas p₁))
      b : (ƛ M′) · N —↠ (ƛ M′) · N′
      b = —↠-congᵣ (par-betas p₂)
      c = (ƛ M′) · N′ —→⟨ —→-β ⟩ M′ [ N′ ] ∎ in
  —↠-trans (—↠-trans a b) c


infix  2 _⇉*_
infixr 2 _⇉⟨_⟩_
infix  3 _∎

data _⇉*_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      ------
    → M ⇉* M

  _⇉⟨_⟩_ : ∀ {n} (L : Term n) {M N : Term n}
    → L ⇉  M
    → M ⇉* N
      ------
    → L ⇉* N

betas-pars : ∀ {n} {M N : Term n}
  → M —↠ N
    ------
  → M ⇉* N
betas-pars (M₁ ∎) = M₁ ∎
betas-pars (L —→⟨ b ⟩ bs) = L ⇉⟨ beta-par b ⟩ betas-pars bs


pars-betas : ∀ {n} {M N : Term n}
  → M ⇉* N
    ------
  → M —↠ N
pars-betas (M ∎) = M ∎
pars-betas (L ⇉⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)
