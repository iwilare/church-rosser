# Formalizations of the Church-Rosser Theorem in Agda

Confluence for the untyped lambda calculus, shown using Takahashi translation with three different methods: Tait and Martin-Löf (1971), Komori-Matsuda-Yamakawa (2014), and the proof by Dehornoy-van Oostrom (2008) later formalized in Nagele-van Oostrom-Sternagel (2016). This code reuses (a simplified version of) the infrastructure for λ-terms and substitutions provided by the [PLFA book](https://plfa.github.io/).

## Files structure

### Terms

- [DeBruijn](DeBruijn): untyped lambda terms with De Bruijn indices.
- [Substitution](Substitution): a simplified version of the [σ-calculus for explicit substitutions from PLFA](https://plfa.github.io/Substitution/), used to show the substitution lemma.

### Semantics

- [Beta](Beta.agda): β-reduction, both one-step and its transitive reflexive closure.
- [BetaSubstitutivity](BetaSubstitutivity.agda): β-reduction for substitutions and substitutivity of β-reduction, i.e.: $M \to^\*\_\beta M'$ and $N \to^\*\_\beta N'$ implies $M[N] \to^\*\_\beta M'[N']$.
- [Parallel](Parallel.agda): one-step and many-steps parallel reduction and conversion with β-reduction.
- [Takahashi](Takahashi.agda): Takahashi translation of a term.

### Confluence

- [ConfluenceParallel](ConfluenceParallel.agda): classic Tait and Martin-Löf method with parallel reduction.
- [ConfluenceParallelTakahashi](ConfluenceParallelTakahashi.agda): parallel reduction with the diamond lemma on Takahashi translation.
- [ConfluenceTakahashi](ConfluenceTakahashi.agda): Komori-Matsuda-Yamakawa proof, just employing Takahashi translation and no parallel reduction.
- [ConfluenceZ](ConfluenceZ.agda): (semi-)confluence by the Z property, using Takahashi translation as map.

## Version

Tested with Agda 2.6.2.
