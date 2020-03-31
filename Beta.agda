import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst₂; cong₂)
open import Data.Nat
open import Data.Fin
open import DeBruijn
open import Substitution

infix 2 _—→_

data _—→_ : ∀ {n} → Term n → Term n → Set where

  —→-ξ₁ : ∀ {n} {L L′ M : Term n}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  —→-ξ₂ : ∀ {n} {L M M′ : Term n}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  —→-β : ∀ {n} {N : Term (suc n)} {M : Term n}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  —→-ƛ : ∀ {n} {N N′ : Term (suc n)}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {n} → Term n → Term n → Set where

  _∎ : ∀ {n} (M : Term n)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {n} {M N : Term n} (L : Term n)
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {n} {M N : Term n}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N



—↠-trans : ∀{n} {L M N : Term n}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ∎)          mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)



appL-cong : ∀ {n} {L L' M : Term n}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {L = L}{M = M} (L ∎) = L · M ∎
appL-cong {L = L}{M = M} (L —→⟨ r ⟩ rs) = L · M —→⟨ —→-ξ₁ r ⟩ appL-cong rs



appR-cong : ∀ {n} {L M M' : Term n}
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {L = L}{M = M} (M ∎) = L · M ∎
appR-cong {L = L}{M = M} (M —→⟨ r ⟩ rs) = L · M —→⟨ —→-ξ₂ r ⟩ appR-cong rs



abs-cong : ∀ {n} {N N' : Term (suc n)}
         → N —↠ N'
           ----------
         → ƛ N —↠ ƛ N'
abs-cong (M ∎) = ƛ M ∎
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ —→-ƛ r ⟩ abs-cong rs

