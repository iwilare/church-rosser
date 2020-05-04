import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin hiding (_+_; #_)
open import DeBruijn

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

--------------------------
-- σ-algebra operations --
--------------------------

⟪_⟫ : ∀ {n m} → Subst n m → Term n → Term m
⟪ σ ⟫ = subst σ

ids : ∀ {n} → Subst n n
ids x = # x

↑ : ∀ {n} → Subst n (suc n)
↑ x = # (suc x)

infix 6 _•_

_•_ : ∀ {n m} → Term m → Subst n m → Subst (suc n) m
(M • σ) zero    = M
(M • σ) (suc x) = σ x

infixr 5 _⨟_

_⨟_ : ∀ {n k m} → Subst n k → Subst k m → Subst n m
σ ⨟ τ = ⟪ τ ⟫ ∘ σ

-------------------------
-- σ-algebra equations --
-------------------------

ren : ∀ {n m} → Rename n m → Subst n m
ren ρ = ids ∘ ρ

sub-head : ∀ {n m} {M : Term m} {σ : Subst n m}
         → ⟪ M • σ ⟫ (# zero) ≡ M
sub-head = refl

sub-tail : ∀ {n m} {M : Term m} {σ : Subst n m}
         → (↑ ⨟ M • σ) ≡ σ
sub-tail = extensionality λ x → refl

sub-idL : ∀ {n m} {σ : Subst n m}
       → ids ⨟ σ ≡ σ
sub-idL = extensionality λ x → refl

sub-dist :  ∀ {n m k} {σ : Subst n m} {τ : Subst m k} {M : Term m}
         → ((M • σ) ⨟ τ) ≡ ((subst τ M) • (σ ⨟ τ))
sub-dist {n}{m}{k}{σ}{τ}{M} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Fin (suc n)} → ((M • σ) ⨟ τ) x ≡ ((subst τ M) • (σ ⨟ τ)) x
  lemma {x = zero} = refl
  lemma {x = suc x} = refl




cong-ext : ∀ {n m}{ρ ρ′ : Rename n m}
   → (ρ ≡ ρ′)
     ---------------------------------
   → ext ρ ≡ ext ρ′
cong-ext{n}{m}{ρ}{ρ′} rr = extensionality λ x → lemma {x}
  where
  lemma : ∀ {x : Fin (suc n)} → ext ρ x ≡ ext ρ′ x
  lemma {zero} = refl
  lemma {suc y} = cong suc (cong-app rr y)

cong-rename : ∀ {n m}{ρ ρ′ : Rename n m}{M M′ : Term n}
        → (ρ ≡ ρ′)  →  M ≡ M′
          ------------------------------
        → rename ρ M ≡ rename ρ′ M
cong-rename {M = # x} rr refl = cong #_ (cong-app rr x)
cong-rename {ρ = ρ} {ρ′ = ρ′} {M = ƛ N} rr refl =
   cong ƛ_ (cong-rename {ρ = ext ρ}{ρ′ = ext ρ′}{M = N} (cong-ext rr) refl)
cong-rename {M = L · M} rr refl =
   cong₂ _·_ (cong-rename rr refl) (cong-rename rr refl)

cong-exts : ∀ {n m}{σ σ′ : Subst n m}
   → (σ ≡ σ′)
     -----------------------------------
   → exts σ ≡ exts σ′
cong-exts{n}{m}{σ}{σ′} ss = extensionality λ x → lemma {x}
   where
   lemma : ∀ {x} → exts σ x ≡ exts σ′ x
   lemma {zero} = refl
   lemma {suc x} = cong (rename suc) (cong-app (ss) x)

cong-sub : ∀ {n m}{σ σ′ : Subst n m}{M M′ : Term n}
            → (σ ≡ σ′)  →  M ≡ M′
              ------------------------------
            → subst σ M ≡ subst σ′ M′
cong-sub {n}{m}{σ}{σ′}{# x} ss refl = cong-app ss x
cong-sub {n}{m}{σ}{σ′}{ƛ M} ss refl =
   cong ƛ_ (cong-sub {σ = exts σ}{σ′ = exts σ′} {M = M} (cong-exts ss) refl)
cong-sub {n}{m}{σ}{σ′}{L · M} ss refl =
   cong₂ _·_ (cong-sub {M = L} ss refl) (cong-sub {M = M} ss refl)

cong-sub-zero : ∀ {n} {M M′ : Term n}
  → M ≡ M′
    -----------------------------------------
  → subst-zero M ≡ (subst-zero M′)
cong-sub-zero {n}{M}{M′} mm′ =
   extensionality λ x → cong (λ z → subst-zero z x) mm′

cong-cons : ∀ {n m}{M N : Term m}{σ τ : Subst n m}
  → M ≡ N  →  (σ ≡ τ)
    --------------------------------
  → (M • σ) ≡ (N • τ)
cong-cons{n}{m}{M}{N}{σ}{τ} refl st = extensionality lemma
  where
  lemma : (x : Fin (suc n)) → (M • σ) x ≡ (M • τ) x
  lemma zero = refl
  lemma (suc x) = cong-app st x

cong-seq : ∀ {n m k}{σ σ′ : Subst n m}{τ τ′ : Subst m k}
  → (σ ≡ σ′) → (τ ≡ τ′)
  → (σ ⨟ τ) ≡ (σ′ ⨟ τ′)
cong-seq {n}{m}{k}{σ}{σ′}{τ}{τ′} ss′ tt′ = extensionality lemma
  where
  lemma : (x : Fin n) → (σ ⨟ τ) x ≡ (σ′ ⨟ τ′) x
  lemma x =
     begin
       (σ ⨟ τ) x
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ cong (subst τ) (cong-app ss′ x) ⟩
       subst τ (σ′ x)
     ≡⟨ cong-sub{M = σ′ x} tt′ refl ⟩
       subst τ′ (σ′ x)
     ≡⟨⟩
       (σ′ ⨟ τ′) x
     ∎




ren-ext : ∀ {n m} {ρ : Rename n m}
        → ren (ext ρ) ≡ exts (ren ρ)
ren-ext {n}{m}{ρ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Fin (suc n)} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = zero} = refl
  lemma {x = suc x} = refl

rename-subst-ren : ∀ {n m} {ρ : Rename n m} {M : Term n}
                 → rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {M = # x} = refl
rename-subst-ren {n}{ρ = ρ}{M = ƛ N} =
  begin
      rename ρ (ƛ N)
    ≡⟨⟩
      ƛ rename (ext ρ) N
    ≡⟨ cong ƛ_ (rename-subst-ren {ρ = ext ρ}{M = N}) ⟩
      ƛ ⟪ ren (ext ρ) ⟫ N
    ≡⟨ cong ƛ_ (cong-sub{M = N} ren-ext refl) ⟩
      ƛ ⟪ exts (ren ρ) ⟫ N
    ≡⟨⟩
      ⟪ ren ρ ⟫ (ƛ N)
  ∎
rename-subst-ren {M = L · M} = cong₂ _·_ rename-subst-ren rename-subst-ren

exts-cons-shift : ∀ {n m} {σ : Subst n m}
                → exts σ  ≡ (# zero • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → lemma{x = x}
  where
  lemma : ∀ {n m} {σ : Subst n m} {x : Fin (suc n)}
                  → exts σ x ≡ (# zero • (σ ⨟ ↑)) x
  lemma {x = zero} = refl
  lemma {x = suc y} = rename-subst-ren

subst-zero-cons-ids : ∀ {n}{M : Term n}
                 → subst-zero M ≡ (M • ids)
subst-zero-cons-ids = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {n}{M : Term n}{x : Fin (suc n)}
        → subst-zero M x ≡ (M • ids) x
  lemma {x = zero} = refl
  lemma {x = suc x} = refl

exts-ids : ∀ {n}
         → exts ids ≡ ids {suc n}
exts-ids {n} = extensionality lemma
  where lemma : (x : Fin (suc n)) → exts ids x ≡ ids x
        lemma zero = refl
        lemma (suc x) = refl

sub-id : ∀ {n} {M : Term n}
         → ⟪ ids ⟫ M ≡ M
sub-id {M = # x} = refl
sub-id {M = ƛ N} =
   begin
     ⟪ ids ⟫ (ƛ N)
   ≡⟨⟩
     ƛ ⟪ exts ids ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} exts-ids refl)  ⟩
     ƛ ⟪ ids ⟫ N
   ≡⟨ cong ƛ_ sub-id ⟩
     ƛ N
   ∎
sub-id {M = L · M} = cong₂ _·_ sub-id sub-id

sub-idR : ∀ {n m} {σ : Subst n m}
       → (σ ⨟ ids) ≡ σ
sub-idR {n}{σ = σ} =
          begin
            σ ⨟ ids
          ≡⟨⟩
            ⟪ ids ⟫ ∘ σ
          ≡⟨ extensionality (λ x → sub-id) ⟩
            σ
          ∎

compose-ext : ∀ {n m k}{ρ : Rename m k} {ρ′ : Rename n m}
            → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′)
compose-ext = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {n m k}{ρ : Rename m k} {ρ′ : Rename n m} {x : Fin (suc n)}
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma {x = zero} = refl
  lemma {x = suc x} = refl

compose-rename : ∀ {n m k}{M : Term n}{ρ : Rename m k}{ρ′ : Rename n m}
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-rename {M = # x} = refl
compose-rename {n}{m}{k}{ƛ N}{ρ}{ρ′} = cong ƛ_ G
  where
  G : rename (ext ρ) (rename (ext ρ′) N) ≡ rename (ext (ρ ∘ ρ′)) N
  G =
      begin
        rename (ext ρ) (rename (ext ρ′) N)
      ≡⟨ compose-rename{ρ = ext ρ}{ρ′ = ext ρ′} ⟩
        rename ((ext ρ) ∘ (ext ρ′)) N
      ≡⟨ cong-rename compose-ext refl ⟩
        rename (ext (ρ ∘ ρ′)) N
      ∎
compose-rename {M = L · M} = cong₂ _·_ compose-rename compose-rename

commute-subst-rename : ∀ {n m}{M : Term n}{σ : Subst n m}
                        {ρ : ∀ {n} → Rename n (suc n)}
     → (∀ {x : Fin n} → exts σ (ρ x) ≡ rename ρ (σ x))
     → subst (exts σ) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = # x} r = r
commute-subst-rename{n}{m}{ƛ N}{σ}{ρ} r =
   cong ƛ_ (commute-subst-rename{suc n}{suc m}{N}
               {exts σ}{ρ = ρ′} (λ {x} → H {x}))
   where
   ρ′ : ∀ {n} → Rename n (suc n)
   ρ′ {zero} = λ ()
   ρ′ {suc n} = ext ρ

   H : {x : Fin (suc n)} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {zero} = refl
   H {suc y} =
     begin
       exts (exts σ) (ext ρ (suc y))
     ≡⟨⟩
       rename suc (exts σ (ρ y))
     ≡⟨ cong (rename suc) r ⟩
       rename suc (rename ρ (σ y))
     ≡⟨ compose-rename ⟩
       rename (suc ∘ ρ) (σ y)
     ≡⟨ cong-rename refl refl ⟩
       rename ((ext ρ) ∘ suc) (σ y)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename suc (σ y))
     ≡⟨⟩
       rename (ext ρ) (exts σ (suc y))
     ∎
commute-subst-rename {M = L · M}{ρ = ρ} r =
   cong₂ _·_ (commute-subst-rename{M = L}{ρ = ρ} r)
             (commute-subst-rename{M = M}{ρ = ρ} r)

exts-seq : ∀ {n m m′} {σ₁ : Subst n m} {σ₂ : Subst m m′}
         → (exts σ₁ ⨟ exts σ₂) ≡ exts (σ₁ ⨟ σ₂)
exts-seq = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {n m m′}{x : Fin (suc n)} {σ₁ : Subst n m}{σ₂ : Subst m m′}
     → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
  lemma {x = zero} = refl
  lemma {x = suc x}{σ₁}{σ₂} =
     begin
       (exts σ₁ ⨟ exts σ₂) (suc x)
     ≡⟨⟩
       ⟪ exts σ₂ ⟫ (rename suc (σ₁ x))
     ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = suc} refl ⟩
       rename suc (⟪ σ₂ ⟫ (σ₁ x))
     ≡⟨⟩
       rename suc ((σ₁ ⨟ σ₂) x)
     ∎

sub-sub : ∀ {n m k}{M : Term n} {σ₁ : Subst n m}{σ₂ : Subst m k}
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub {M = # x} = refl
sub-sub {n}{m}{k}{ƛ N}{σ₁}{σ₂} =
   begin
     ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ (ƛ N))
   ≡⟨⟩
     ƛ ⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ N)
   ≡⟨ cong ƛ_ (sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
     ƛ ⟪ exts σ₁ ⨟ exts σ₂ ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} exts-seq refl) ⟩
     ƛ ⟪ exts ( σ₁ ⨟ σ₂) ⟫ N
   ∎
sub-sub {M = L · M} = cong₂ _·_ (sub-sub{M = L}) (sub-sub{M = M})

rename-subst : ∀ {n m m′}{M : Term n}{ρ : Rename n m}{σ : Subst m m′}
             → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {n}{m}{m′}{M}{ρ}{σ} =
   begin
     ⟪ σ ⟫ (rename ρ M)
   ≡⟨ cong ⟪ σ ⟫ (rename-subst-ren{M = M}) ⟩
     ⟪ σ ⟫ (⟪ ren ρ ⟫ M)
   ≡⟨ sub-sub{M = M} ⟩
     ⟪ ren ρ ⨟ σ ⟫ M
   ≡⟨⟩
     ⟪ σ ∘ ρ ⟫ M
   ∎

sub-assoc : ∀ {n m k Ψ} {σ : Subst n m} {τ : Subst m k} {θ : Subst k Ψ}
          → (σ ⨟ τ) ⨟ θ ≡ (σ ⨟ τ ⨟ θ)
sub-assoc {n}{m}{k}{Ψ}{σ}{τ}{θ} = extensionality λ x → lemma{x = x}
  where
  lemma : ∀ {x : Fin n} → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
  lemma {x} =
      begin
        ((σ ⨟ τ) ⨟ θ) x
      ≡⟨⟩
        ⟪ θ ⟫ (⟪ τ ⟫ (σ x))
      ≡⟨ sub-sub{M = σ x} ⟩
        ⟪ τ ⨟ θ ⟫ (σ x)
      ≡⟨⟩
        (σ ⨟ τ ⨟ θ) x
      ∎

subst-zero-exts-cons : ∀ {n m}{σ : Subst n m}{M : Term m}
                     → exts σ ⨟ subst-zero M ≡ (M • σ)
subst-zero-exts-cons {n}{m}{σ}{M} =
    begin
      exts σ ⨟ subst-zero M
    ≡⟨ cong-seq exts-cons-shift subst-zero-cons-ids ⟩
      (# zero • (σ ⨟ ↑)) ⨟ (M • ids)
    ≡⟨ sub-dist ⟩
      (⟪ M • ids ⟫ (# zero)) • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong-cons (sub-head{σ = ids}) refl ⟩
      M • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong-cons refl (sub-assoc{σ = σ}) ⟩
      M • (σ ⨟ (↑ ⨟ (M • ids)))
    ≡⟨ cong-cons refl (cong-seq{σ = σ} refl (sub-tail{M = M}{σ = ids})) ⟩
      M • (σ ⨟ ids)
    ≡⟨ cong-cons refl (sub-idR{σ = σ}) ⟩
      M • σ
    ∎

subst-commute : ∀ {n m} {N : Term (suc n)} {M : Term n} {σ : Subst n m}
  → ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {n} {m} {N} {M} {σ} =
  begin
    ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
  ≡⟨⟩
    ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
  ≡⟨ cong-sub {M = ⟪ exts σ ⟫ N} subst-zero-cons-ids refl ⟩
    ⟪ ⟪ σ ⟫ M • ids ⟫ (⟪ exts σ ⟫ N)
  ≡⟨ sub-sub {M = N} ⟩
    ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) • ids) ⟫ N
  ≡⟨ cong-sub {M = N} (cong-seq exts-cons-shift refl) refl ⟩
  ⟪ (# zero • (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M • ids) ⟫ N
  ≡⟨ cong-sub {M = N} (sub-dist {M = # zero}) refl ⟩
    ⟪ ⟪ ⟪ σ ⟫ M • ids ⟫ (# zero) • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
  ≡⟨⟩
    ⟪ ⟪ σ ⟫ M • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
  ≡⟨ cong-sub {M = N} (cong-cons refl (sub-assoc {σ = σ})) refl ⟩
    ⟪ ⟪ σ ⟫ M • (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M • ids) ⟫ N
  ≡⟨ cong-sub {M = N} refl refl ⟩
    ⟪ ⟪ σ ⟫ M • (σ ⨟ ids) ⟫ N
  ≡⟨ cong-sub {M = N} (cong-cons refl (sub-idR {σ = σ})) refl ⟩
    ⟪ ⟪ σ ⟫ M • σ ⟫ N
  ≡⟨ cong-sub {M = N} (cong-cons refl (sub-idL {σ = σ})) refl ⟩
    ⟪ ⟪ σ ⟫ M • (ids ⨟ σ) ⟫ N
  ≡⟨ cong-sub {M = N} (sym sub-dist) refl ⟩
    ⟪ M • ids ⨟ σ ⟫ N
  ≡⟨ sym (sub-sub {M = N}) ⟩
    ⟪ σ ⟫ (⟪ M • ids ⟫ N)
  ≡⟨ cong ⟪ σ ⟫ (sym (cong-sub {M = N} subst-zero-cons-ids refl)) ⟩
    ⟪ σ ⟫ (N [ M ])
  ∎

rename-subst-commute : ∀ {n m} {N : Term (suc n)} {M : Term n} {ρ : Rename n m }
  → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {n} {m} {N} {M} {ρ} =
  begin
    (rename (ext ρ) N) [ rename ρ M ]
  ≡⟨ cong-sub (cong-sub-zero (rename-subst-ren {M = M})) (rename-subst-ren {M = N}) ⟩
    (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
  ≡⟨ cong-sub refl (cong-sub {M = N} ren-ext refl) ⟩
    (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
  ≡⟨ subst-commute {N = N} ⟩
    subst (ren ρ) (N [ M ])
  ≡⟨ sym (rename-subst-ren) ⟩
    rename ρ (N [ M ])
  ∎

infix 8 _〔_〕

_〔_〕 : ∀ {n}
        → Term (suc (suc n))
        → Term n
          ------------
        → Term (suc n)
_〔_〕 N M =
   subst (exts (subst-zero M)) N

substitution-lemma : ∀{n}{M : Term (suc (suc n))}{N : Term (suc n)}{L : Term n}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution-lemma{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})
