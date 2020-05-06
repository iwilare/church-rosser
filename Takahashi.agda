open import DeBruijn


infix 8 _*

_* : ∀ {n} → Term n → Term n
(# x) *       = # x
(ƛ M) *       = ƛ M *
((ƛ M) · N) * = M * [ N * ]
(L · N) *     = L * · N *
