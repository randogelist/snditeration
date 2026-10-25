# Zetahyperbolic — Lean 4.33.0 formalization

This is **source-level** formalization of the 52-page manuscript
*Spectral Theory and Diophantine Bounds for Hankel Determinants of Odd Zeta
Values* (21 October 2026), using Lean 4.33.0 and a pinned Mathlib4 commit.

The repository's historical ZIP checkpoint uploads are retained unchanged.
Unlike those archives, these `.lean` files are directly buildable, importable,
and covered by GitHub Actions. The source provenance is the local
GOODWORKFLOWFRONTIER/ManuscriptChain formalization.

## Getting started

```sh
lake update
lake exe cache get
lake build Zetahyperbolic
lake env lean Zetahyperbolic/Audit.lean
```

On Windows with a compatible prepopulated Mathlib/LEAN_ANCHORINGS cache, run
`run.cmd`; the script performs no automatic cache-download operation and
only builds current project modules. The first installation or a changed
dependency fingerprint requires provisioning Mathlib separately.

## Current scope

* `Zetahyperbolic/Section2/Moments.lean`: Definition 2.1, rational pole
  and monomial formulas, and the affine Hankel pencil.
* `Zetahyperbolic/Section2/BasisInvariance.lean`: Theorem 2.4's
  general rational change-of-basis determinant identity and integer
  primitive normalization up to sign. Its constructed manuscript
  specialization requires `delta p ≠ 0`; Section 2.5 will discharge that
  assumption from explicit pole data.
* `Zetahyperbolic/Audit.lean`: explicit `#print axioms` checks.

**Do not infer** the claimed irrationality of ζ(5), ζ(7), or their linear
forms from these foundation modules. The analytic and arithmetic endpoint
bounds in Sections 3–6 remain outside this initial build.

This branch is proposed as a PR, not merged into `main`.
See [the proof ledger](docs/FORMALIZATION_LEDGER.md).
