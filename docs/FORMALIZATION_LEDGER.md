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
| Theorem 2.4 | `Section2/BasisInvariance.lean` | **A-Tier exact source declarations:** generic determinant congruence, primitive normalization and concrete manuscript basis invariance; nonzero determinant is discharged by the Section 2.5 pole algebra. Passed build and transitive dependency audit in PRs #1-#2. |
| Theorem 2.5 | `Section2/PoleDiagonalization.lean` | **A-Tier algebraic core:** actual residue coefficients, nonzero γ, Vandermonde factorization, invertible slope, exact determinant degree h and affine transformed pencil. Missing from this branch: explicit interpolation-polynomial construction/equality with the rational-function Lagrange basis. PR #2 CI passed. |
| Theorem 3.1 | `Section3/SymmetricAffinePencil.lean`, `Section3/ConcretePencil.lean` in PR #4 | **In progress / not yet merged:** manuscript determinant evaluation and conditional positive-Gram bridge. Unconditional moment integral identity (3.2), positive definite Gram and full real-root/zero-free radius transfer remain open in GitHub `main`. |
| Theorem 4.1 | `Section4/Transfer.lean` | **A-Tier conditional arithmetic transfer** (PR #3 CI passed): local comparison + evaluation decay + index budget entail quantitative rational exclusion and irrationality. The paper's asymptotic root-gap → index-budget selection and effective b₀ are not yet proved in GitHub. NOT an unconditional zeta irrationality proof. |
| Theorems 4.4-4.5 | — | Open: ζ(5) root-norm bound, integrality and complete effective measures. |
| Theorems 5.1-5.2 | — | Open: ζ(7) Beukers moments and dual pencil. |
| Section 6 | — | Open: multivariable and character endpoints. |

A-Tier **requires both** a successful Lean build and an axiom audit, with
no `sorryAx`, new axioms, or unmentioned hypotheses. Passing source parsing
alone never promotes an open paper theorem to proven status.

Future PRs should follow the manuscript chronology, reuse unchanged
compiler-certified modules, and preserve the audit/CI evidence.

## Verified GitHub gates (October 25, 2026)

- PR #1: https://github.com/randogelist/snditeration/pull/1 — build+dependency audit PASS; merged `6faec4c`.
- PR #2: https://github.com/randogelist/snditeration/pull/2 — build+dependency audit PASS; merged `297cd4f`.
- PR #3: https://github.com/randogelist/snditeration/pull/3 — build+dependency audit PASS; merged `8e6f44e`.
- A checkpoint is an exact Lean declaration with a known CI receipt, not a claim that the entire paper theorem is manuscript-equivalent.
