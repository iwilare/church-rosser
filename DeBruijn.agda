import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin hiding (_+_; #_)

---------------------------
-- Definition of ƛ-terms --
---------------------------

infix  9  #_
infixl 7  _·_
infix  6  ƛ_

data Term : ℕ → Set where
  #_  : ∀ {n : ℕ} → Fin n           → Term n
  ƛ_  : ∀ {n : ℕ} → Term (suc n)    → Term n
  _·_ : ∀ {n : ℕ} → Term n → Term n → Term n

----------------------------
-- de Bruijn substitution --
----------------------------

Rename : ℕ → ℕ → Set
Rename n m = Fin n → Fin m

Subst : ℕ → ℕ → Set
Subst n m = Fin n → Term m

ext : ∀ {n m} → Rename n m → Rename (suc n) (suc m)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : ∀ {n m} → Rename n m → (Term n → Term m)
rename ρ (# x)   = # (ρ x)
rename ρ (ƛ N)   = ƛ (rename (ext ρ) N)
rename ρ (L · M) = (rename ρ L) · (rename ρ M)

exts : ∀ {n m} → Subst n m → Subst (suc n) (suc m)
exts σ zero    = # zero
exts σ (suc x) = rename suc (σ x)

subst : ∀ {n m} → Subst n m → (Term n → Term m)
subst σ (# k)   = σ k
subst σ (ƛ N)   = ƛ (subst (exts σ) N)
subst σ (L · M) = subst σ L · subst σ M

subst-zero : ∀ {n} → Term n → Subst (suc n) n
subst-zero M zero    = M
subst-zero M (suc x) = # x

infix 8 _[_]

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
M [ N ] = subst (subst-zero N) M

