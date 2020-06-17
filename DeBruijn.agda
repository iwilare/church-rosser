open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)


infix  9  #_
infixl 7  _·_
infix  6  ƛ_

data Term : ℕ → Set where
  #_  : ∀ {n : ℕ} → Fin n           → Term n
  ƛ_  : ∀ {n : ℕ} → Term (suc n)    → Term n
  _·_ : ∀ {n : ℕ} → Term n → Term n → Term n


Rename : ℕ → ℕ → Set
Rename n m = Fin n → Fin m

Subst : ℕ → ℕ → Set
Subst n m = Fin n → Term m

ext : ∀ {n m} → Rename n m → Rename (suc n) (suc m)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : ∀ {n m} → Rename n m → (Term n → Term m)
rename ρ (# x)   = # (ρ x)
rename ρ (ƛ M)   = ƛ (rename (ext ρ) M)
rename ρ (M · N) = rename ρ M · rename ρ N

exts : ∀ {n m} → Subst n m → Subst (suc n) (suc m)
exts σ zero    = # zero
exts σ (suc x) = rename suc (σ x)

subst : ∀ {n m} → Subst n m → (Term n → Term m)
subst σ (# x)   = σ x
subst σ (ƛ M)   = ƛ (subst (exts σ) M)
subst σ (M · N) = subst σ M · subst σ N

subst-zero : ∀ {n} → Term n → Subst (suc n) n
subst-zero M zero    = M
subst-zero M (suc x) = # x


infix 8 _[_]

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
M [ N ] = subst (subst-zero N) M
