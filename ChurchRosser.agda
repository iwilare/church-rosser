open import Data.Product
open import DeBruijn
open import Substitution
open import Parallel
open import Beta

---------------------------
-- Takahashi translation --
---------------------------

infix 8 _*

_* : ∀{n} → Term n → Term n
(# x) *       = # x
(ƛ N) *       = ƛ N *
((ƛ N) · M) * = N * [ M * ] 
(L · M) *     = L * · M *

--------------------------------------------------------------------------
-- Theorem 5 - Parallel Reductions in Lambda Calculus (Takahashi, 1987) --
--------------------------------------------------------------------------

theorem5 : ∀{n} {M N : Term n} → M ⇉ N → N ⇉ M *
theorem5 {M = # x} ⇉-c = ⇉-c
theorem5 {M = ƛ M} (⇉-ƛ M⇉N) = ⇉-ƛ (theorem5 M⇉N)
theorem5 {M = (ƛ N) · M} (⇉-β N⇉N′ M⇉M′) = sub-par (theorem5 N⇉N′) (theorem5 M⇉M′)

{-
  Agda non riesce a capire che M · N non è una β-reduct per quindi poter
  applicare L * · M * ≡ (L · M) *, pur essendo l'unica possibilità dato
  che il caso con L = ƛ x ⇒ x₁ è trattato separatamente.
  Bisogna per questo fare case-splitting sul primo termine e analizzare caso per caso.
-}

theorem5 {M = # _   · N} (⇉-ξ M′ N′)       = ⇉-ξ (theorem5 M′) (theorem5 N′)
theorem5 {M = (ƛ N) · M} (⇉-ξ (⇉-ƛ M′) N′) = ⇉-β (theorem5 M′) (theorem5 N′)
theorem5 {M = _ · _ · N} (⇉-ξ M′ N′)       = ⇉-ξ (theorem5 M′) (theorem5 N′)

-------------------------------------------------------
-- Confluence for parallel reduction using theorem 5 --
-------------------------------------------------------

confluent⇉ : ∀{n} {M A B : Term n}
           → M ⇉ A  →  M ⇉ B
    --------------------------
  → ∃[ N ] ((A ⇉ N) × (B ⇉ N))
confluent⇉ {M = M} M⇉A M⇉B = M * , theorem5 M⇉A , theorem5 M⇉B

-----------------
-- Strip lemma --
-----------------

strip : ∀{n} {M N N′ : Term n}
           → (M ⇉ N) → (M ⇉* N′)
    ----------------------------
  → ∃[ L ] ((N ⇉* L) × (N′ ⇉ L))
strip{n}{M}{N} mn (_ ∎) = N , (N ∎) , mn
strip{n}{M}{N} mn (M ⇉⟨ mm' ⟩ m'n')
    with confluent⇉ mn mm'
... | L , nl , m'l 
      with strip m'l m'n'
...   | L′ , ll'             , n'l' =
        L′ , (N ⇉⟨ nl ⟩ ll') , n'l'
        
-------------------------------------------
-- Confluence of parallel reduction star --
-------------------------------------------

confluent⇉* : ∀{n} {L A B : Term n}
           → L ⇉* A  →  L ⇉* B
    ------------------------------
  → ∃[ L ] ((A ⇉* L) × (B ⇉* L))
confluent⇉*{B = N} (L ∎) L⇉*N = N , L⇉*N , (N ∎)
confluent⇉*{n}{L}{A′}{B} (L ⇉⟨ L⇉A ⟩ A⇉*A′) L⇉*B
    with strip L⇉A L⇉*B
... | N , A⇉*N , B⇉N
      with confluent⇉* A⇉*A′ A⇉*N
...   | N′ , A′⇉*N′ , N⇉*N′ =
        N′ , A′⇉*N′ , (B ⇉⟨ B⇉N ⟩ N⇉*N′)

---------------------------------------
-- Confluence of beta reduction star --
---------------------------------------

confluent—↠ : ∀{n} {L A B : Term n}
           → L —↠ A  →  L —↠ B
    ------------------------------
  → ∃[ R ] ((A —↠ R) × (B —↠ R))
confluent—↠ L↠A L↠B
    with confluent⇉* (betas-pars L↠A) (betas-pars L↠B)
... | N , A⇉N , B⇉N =
      N , pars-betas A⇉N , pars-betas B⇉N
