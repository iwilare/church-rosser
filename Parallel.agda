import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst₂; cong)
open import Data.Nat.Base
open import Data.Fin hiding (_+_; #_)
open import Data.Product using (∃; _×_; _,_; ∃-syntax)
open import DeBruijn
open import Substitution
open import Beta

--------------------------------------------
-- Definition of parallel β-reduction (⇉) --
--------------------------------------------

infix 4 _⇉_

data _⇉_ : ∀ {n} → Term n → Term n → Set where

  ⇉-c : ∀ {n} {x : Fin n}
      ---------
    → # x ⇉ # x

  ⇉-ƛ : ∀ {n} {M N : Term (suc n)}
    → M ⇉ N
      ---------
    → ƛ M ⇉ ƛ N

  ⇉-ξ : ∀ {n} {N N′ M M′ : Term n}
    → N ⇉ N′
    → M ⇉ M′
      ---------------
    → N · M ⇉ N′ · M′

  ⇉-β : ∀{n} {N N′ : Term (suc n)}{M M′ : Term n}
    → N ⇉ N′
    → M ⇉ M′
      ---------------------
    → (ƛ N) · M ⇉ N′ [ M′ ]

par-subst : ∀{n m} → Subst n m → Subst n m → Set
par-subst {n}{m} σ σ′ = ∀{x : Fin n} → σ x ⇉ σ′ x


par-rename : ∀{n m} {ρ : Rename n m} {M M′ : Term n}
  → M ⇉ M′
    ------------------------
  → rename ρ M ⇉ rename ρ M′
par-rename ⇉-c = ⇉-c
par-rename (⇉-ƛ p) = ⇉-ƛ (par-rename p)
par-rename (⇉-ξ p₁ p₂) = ⇉-ξ (par-rename p₁) (par-rename p₂)
par-rename {n}{m}{ρ} (⇉-β {n}{N}{N′}{M}{M′} p₁ p₂)
    with ⇉-β (par-rename{ρ = ext ρ} p₁) (par-rename{ρ = ρ} p₂)
... | G rewrite rename-subst-commute{n}{m}{N′}{M′}{ρ} = G


par-subst-exts : ∀{n m} {σ τ : Subst n m}
  → par-subst σ τ
    ------------------------------------------
  → par-subst (exts σ) (exts τ)
par-subst-exts s {x = zero} = ⇉-c
par-subst-exts s {x = suc x} = par-rename s


subst-par : ∀{n m} {σ τ : Subst n m} {M M′ : Term n}
  → par-subst σ τ → M ⇉ M′
    ----------------------
  → subst σ M ⇉ subst τ M′
subst-par {M = # x} s ⇉-c = s
subst-par {n}{m}{σ}{τ} {ƛ N} s (⇉-ƛ p) =
  ⇉-ƛ (subst-par {σ = exts σ} {τ = exts τ}
        (λ {x} → par-subst-exts s {x = x}) p)
subst-par {M = L · M} s (⇉-ξ p₁ p₂) =
  ⇉-ξ (subst-par s p₁) (subst-par s p₂)
subst-par {n}{m}{σ}{τ} {(ƛ N) · M} s (⇉-β {N′ = N′}{M′ = M′} p₁ p₂)
    with ⇉-β (subst-par{σ = exts σ}{τ = exts τ}{M = N}
                        (λ{x} → par-subst-exts s {x = x}) p₁)
               (subst-par {σ = σ} s p₂)
... | G rewrite subst-commute{N = N′}{M = M′}{σ = τ} = G

par-subst-zero : ∀ {n} {M M′ : Term n}
       → M ⇉ M′
       → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero {M} {M′} p {zero} = p
par-subst-zero {M} {M′} p {suc x} = ⇉-c

sub-par : ∀{n} {N N′ : Term (suc n)} {M M′ : Term n}
  → N ⇉ N′
  → M ⇉ M′
    --------------------
  → N [ M ] ⇉ N′ [ M′ ]
sub-par pn pm = subst-par (par-subst-zero pm) pn

--------------------------------------------
-- Parallel reduction implies β-reduction --
--------------------------------------------

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
beta-par {M = L · M} (—→-ξ₁ r) = ⇉-ξ (beta-par {M = L} r) par-refl
beta-par {M = L · M} (—→-ξ₂ r) = ⇉-ξ par-refl (beta-par {M = M} r)
beta-par {M = ƛ N} (—→-ƛ r) = ⇉-ƛ (beta-par r)
beta-par {M = (ƛ N) · M} —→-β = ⇉-β par-refl par-refl


par-betas : ∀ {n} {M N : Term n}
  → M ⇉ N
    ------
  → M —↠ N
par-betas {M = (# _)} (⇉-c {x = x}) = # x ∎
par-betas {M = ƛ N} (⇉-ƛ p) = abs-cong (par-betas p)
par-betas {M = L · M} (⇉-ξ p₁ p₂) =
   —↠-trans (appL-cong (par-betas p₁))
            (appR-cong (par-betas p₂))
par-betas {M = (ƛ N) · M} (⇉-β {N′ = N′}{M′ = M′} p₁ p₂) =
  let a : (ƛ N) · M —↠ (ƛ N′) · M
      a = appL-cong (abs-cong (par-betas p₁)) 
      b : (ƛ N′) · M —↠ (ƛ N′) · M′
      b = appR-cong (par-betas p₂)
      c = (ƛ N′) · M′ —→⟨ —→-β ⟩ N′ [ M′ ] ∎ in
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
betas-pars {n} {.L} {N} (L —→⟨ b ⟩ bs) =
   L ⇉⟨ beta-par b ⟩ betas-pars bs


pars-betas : ∀ {n} {M N : Term n}
  → M ⇉* N
    ------
  → M —↠ N
pars-betas (M ∎) = M ∎
pars-betas (L ⇉⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)
