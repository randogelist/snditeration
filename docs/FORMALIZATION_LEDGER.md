# Manuscript-to-Lean ledger — YOU_ARE_GOODWORKFLOWFRONTIER

Manuscript: 52-page paper, dated 21 October 2026.
Compiler: Lean 4.33.0. Mathlib pin: `db584cd6d46c92f209a44c0f1c829460d327499d`.
GitHub checkpoint: `ZETA_HYPERBOLIC_ANCHOR_7` (source migration, not a newly
asserted proof).

| Paper item | Source | State / dependency |
| --- | --- | --- |
| Definition 2.1 (2.1)-(2.3), (2.8)-(2.9) | `Section2/Moments.lean` | Definitions of D, harmonic numbers, moments, residues and affine pencil integrated. General rational-function linearity/uniqueness not yet established. |
| Lemma 2.2 (2.5) | — | Open: pullback of full rational function domain. |
| Lemma 2.3 (2.6)-(2.7) | — | Open: reflection/difference for general rational-function span. |
| Theorem 2.4 | `Section2/BasisInvariance.lean` | Constructed proof of generic determinant change, normalization and conditional manuscript instantiation; concrete nonzero determinant depends on Theorem 2.5. Await GitHub CI build + axiom audit for this commit. |
| Theorem 2.5 | — | Open: Vandermonde residue factorization and nonzero gamma over actual poles. Prior ZIP branches contain candidate formalizations, not imported or freshly checked here. |
| Theorem 3.1 | — | Open: actual positive Gram realization (3.2) and real-root transfer. |
| Theorem 4.1 | — | Open: effective irrationality transfer under spectral hypotheses. |
| Theorems 4.4-4.5 | — | Open: ζ(5) root-norm bound, integrality and complete effective measures. |
| Theorems 5.1-5.2 | — | Open: ζ(7) Beukers moments and dual pencil. |
| Section 6 | — | Open: multivariable and character endpoints. |

A-Tier **requires both** a successful Lean build and an axiom audit, with
no `sorryAx`, new axioms, or unmentioned hypotheses. Passing source parsing
alone never promotes an open paper theorem to proven status.

Future PRs should follow the manuscript chronology, reuse unchanged
compiler-certified modules, and preserve the audit/CI evidence.
