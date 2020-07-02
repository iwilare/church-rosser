open import Relation.Binary.Core using (Rel; Reflexive; Trans)
open import Level using (Level; _⊔_; suc)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax;  ∃-syntax; proj₁; proj₂)


data Star {t r} {T : Set t} (R : Rel T r) : Rel T (t ⊔ r) where
  ε   : Reflexive (Star R)
  _▻_ : Trans (Star R) R (Star R)


_▻▻_ : ∀ {t r} {T : Set t} {R : Rel T r} {M L N : T}
  → Star R M L
  → Star R L N
  → Star R M N
ML ▻▻ ε = ML
ML ▻▻ (LL′ ▻ L′N) = (ML ▻▻ LL′) ▻ L′N


Semi-Confluence : ∀ {t r} {T : Set t} (R : Rel T r) → Set (t ⊔ r)
Semi-Confluence R = ∀ {M A B}
  →              R M A → Star R M B
    --------------------------------
  → ∃[ N ] (Star R A N × Star R B N)


Confluence : ∀ {t r} {T : Set t} (R : Rel T r) → Set (t ⊔ r)
Confluence R = ∀ {M A B}
  →         Star R M A → Star R M B
    --------------------------------
  → ∃[ N ] (Star R A N × Star R B N)


semi-to-confluence : ∀ {t r} {T : Set t} {R : Rel T r} →
  Semi-Confluence R → Confluence R
semi-to-confluence sc {B = B} ε M*B = B , M*B , ε
semi-to-confluence sc (M*M′ ▻ M′A) M*B
    with semi-to-confluence sc M*M′ M*B
... | N , M′*N , B*N
    with sc M′A M′*N
... | N′ , A*N′ , N*N′
    = N′ , A*N′ , B*N ▻▻ N*N′


Z : ∀ {t r} {T : Set t} (R : Rel T r) → Set (t ⊔ r)
Z {t}{r}{T} R =
  Σ[ _* ∈ (T → T) ]
      (∀ {A B : T} → R A B → Star {t}{r} R B     (A *))
    × (∀ {A B : T} → R A B → Star {t}{r} R (A *) (B *))


z-monotonic : ∀ {t r} {T : Set t} {R : Rel T r}
  → (z : Z R)
    ------------------------------------------
  → (∀ {A B} → Star R A B
             → Star R (proj₁ z A) (proj₁ z B))
z-monotonic z ε = ε
z-monotonic z@(_* , Z₁ , Z₂) (A*A′ ▻ A′B) = z-monotonic z A*A′ ▻▻ Z₂ A′B


z-semi-confluence : ∀ {t r} {T : Set t} {R : Rel T r} →
  Z R → Semi-Confluence R
z-semi-confluence   (_* , Z₁ , Z₂) {A = A} MA ε = A , ε , (ε ▻ MA)
z-semi-confluence z@(_* , Z₁ , Z₂) MA (_▻_ {j = M′} M*M′ M′B) =
   M′ * , Z₁ MA ▻▻ z-monotonic z M*M′ , Z₁ M′B


z-confluence : ∀ {t r} {T : Set t} {R : Rel T r} →
  Z R → Confluence R
z-confluence z = semi-to-confluence (z-semi-confluence z)
