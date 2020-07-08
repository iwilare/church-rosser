open import Relation.Binary.Core
open import Level using (Level; _⊔_; suc)
open import Data.Product using (Σ; _×_; _,_; Σ-syntax;  ∃-syntax; proj₁; proj₂)
open import Function

open import DeBruijn
open import Beta
open import Takahashi
open import Z
open import ConfluenceTakahashi using (lemma3-3; lemma3-5)


star-left :  ∀ {n} {M L N : Term n}
  → M —→ L
  → Star _—→_ L N
    -------------
  → Star _—→_ M N
star-left ML ε = ε ▻ ML
star-left ML (L*N′ ▻ N′N) =
  star-left ML L*N′ ▻ N′N


betas-star : ∀ {n} {M N : Term n}
  → M —↠ N
    -------------
  → Star _—→_ M N
betas-star (M ∎) = ε
betas-star (M —→⟨ M—→M′ ⟩ M′—↠N) =
  star-left M—→M′ (betas-star M′—↠N)


z-confluence-beta : ∀ {n} → Confluence (_—→_ {n})
z-confluence-beta = z-confluence ( _*
                                 , betas-star ∘ lemma3-3
                                 , betas-star ∘ lemma3-5)
