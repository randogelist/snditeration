# Zetahyperbolic — persistent paper-gap tracker for `snditeration`

**Branch:** `persistent/zetahyperbolic-paper-gap-tracker`  
**Purpose:** maintain a persistent, source-linked inventory of **what still needs to be proved or corrected** to formalize the original 52-page, 21 October 2026 Zetahyperbolic manuscript in `snditeration`.

This is a **tracking branch**, not a competing theorem implementation or a declaration that the paper is finished. The comprehensive **45-item gap-by-gap analysis, dependency graph, prioritized proof queue and acceptance gates** are in **[PAPER_GAP_TRACKER.md](docs/PAPER_GAP_TRACKER.md)**.

## What is already established in `snditeration`

The pinned [main checkpoint](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/CHECKPOINT.json) reports **846 audited Lean theorem declarations** (including generated declarations), with [passing CI](https://github.com/randogelist/snditeration/actions/runs/40186793090), Lean **4.33.0** and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. It includes substantial *actual-family* mathematics, not merely abstract theorem wrappers:

- Section 2: actual rational-function domains, pullback/reflection, finite-difference algebra, polynomial-basis transport, Lagrange pole diagonalization.
- Section 3: positive hyperbolic moment measure and exact Gram realization; **Theorem 3.1**'s unconditional real roots, primitive degree and sharp operator-norm zero-free disk; spectral inertia/sign parity and root-side counts; principal-root reality; corrected reciprocal-moment estimates and limit.
- Section 4: a proved **conditional arithmetic transfer**, not its actual-family growth/decay assumptions.

See [the frozen local proof ledger](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/docs/FORMALIZATION_LEDGER.md). These 846 declarations must not be mistaken for 846 complete printed results.

## Highest-priority missing pieces

| Priority | Exact unresolved paper endpoint | Concrete closure target |
|:---|:---|:---|
| P1 | **Lemma 2.3** | Prove that the canonical partial-fraction coefficient equals the actual normalized `iteratedDeriv` at 0, with regularity at the origin |
| P2 | **Theorem 3.3(1)** | All mixed Hankel minors strictly positive, plus the Carleman/Stieltjes determinacy proof; the sign/inertia clauses are already locally proved |
| P3 | **Theorem 3.4; Corollaries 3.5–3.6; Theorem 3.7** | Rank-sensitive interlacing, all-order Dodgson, corrected Lanczos fraction, finite-rank moment laws and actual Newton/Turán equality cases |
| P4 | **Theorems 3.8–3.9; Propositions 4.2–4.3; Theorem 5.4** | Actual Christoffel–Darboux/Hurwitz/character identifications and selective, audited reuse of cross-branch results |
| P5 | **Theorems 4.4–4.8** | Real ζ(5) arithmetic multipliers and determinant decay, `‖B_K‖ ≤ exp(11.411 K)`, height/prime estimates, the asserted irrationality exponent **25687** and linear-form transfer |
| P6 | **Sections 5–6** | Actual ζ(7)/β Beukers integrals, infinite Krein/tail bounds, prime sums, double/triple pole valuations, multiweight positivity and arithmetic conclusions |

**Do not try to prove the literally false printed clauses unchanged.** The audit flags: the continuous-density normalization in 3.2; the unnormalized J-fraction in 3.5; all-order strict finite-atomic Hankel positivity / reversed estimate in 3.6; unjustified coefficient-nonvanishing in 3.7; and more serious proposed repairs for 5.6, 6.3, 6.13 and 6.15. The full register separates *proved counterexamples, suspected argument gaps, corrected variants and open theorems*.

## Cross-branch intake is useful, not automatic proof

The independent [Leaned Paper repository](https://github.com/randogelist/zetahyperbolic-axiom) reports a [passing 219-module audit](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) and **7 complete, 21 partial, 10 not formalized, 7 blocked** printed items. Its completed 4.3 and 5.4 and Section 2/3/4 developments are promising selective imports; **none is automatically certified in `snditeration`**. The wide [`feat/zetahyperbolic-continuation-20261025`](https://github.com/randogelist/snditeration/tree/feat/zetahyperbolic-continuation-20261025) supplies many candidate Section 2–6 files but [failed CI](https://github.com/randogelist/snditeration/actions/runs/40188938699) and cannot be credited as A-Tier.

## How this branch stays persistent

Update [the gap ledger](docs/PAPER_GAP_TRACKER.md) after every accepted proof, with **the literal manuscript statement, exact Lean declaration, source commit, compiler/axiom-audit receipt, hypotheses and what remains**. Freeze already proved modules unless their source or dependencies change. Track source integration, compiled lemmas, whole printed theorems and corrected statements separately. Keep historical ZIP archives unchanged.

### Running the underlying Lean project

The active code remains on [`main`](https://github.com/randogelist/snditeration/tree/main). Use the installed Lean 4.33.0 and matching cached Mathlib to run `run.cmd` in the repository root, or `lake build Zetahyperbolic` followed by `lake env lean Zetahyperbolic/Audit.lean`. This documentation-only branch update does **not** claim a new compiler pass.

**Current manuscript completion: OPEN.** No unconditional irrationality of ζ(5) or ζ(7), RH, or S-Tier finite-witness admission is established here.
