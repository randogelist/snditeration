# Freeze target: P04.03 — complex p-adic zero-free disk

Branch: `feat/zetahyperbolic-p04-03-complex-padic-disk`.
Target: *Proposition 4.3*, original 52-page PDF dated 21 October 2026, p. 15.
Compiler: Lean 4.33.0. Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Exact mathematical statement

For prime q, integral center ξ∈ℤ_q and integer polynomial Q∈ℤ[X], with Q(ξ)≠0, each α∈ℂ_q in the open ball ‖α−ξ‖<‖Q(ξ)‖ satisfies ‖Q(α)‖=‖Q(ξ)‖ and Q(α)≠0.

Code layers:
- `Section4/PadicDisk.lean` generic ultrametric norm and ℚ_q case.
- `Section4/IsometricExtension.lean` arbitrary norm-preserving ultrametric field extension.
- `Section4/ComplexPadicDisk.lean` ℂ_q case via Mathlib's isometric inclusion.
- `Section4/ActualPrimitivePadicDisk.lean` exact original integer-polynomial theorem and specialization to `ManuscriptChain.primitivePolynomial`.

Source provenance: companion `randogelist/zetahyperbolic-axiom@86ca99a23d65cde4880a9005a49076c43e7bc968`, already passing source-level audit. The three imported proof bodies retain original namespaces; only the two Lean import path strings are changed.

### Critical limits

The proposition **assumes** nonzero Q(ξ) at a chosen integral p-adic center. This result does **not** establish p-adic nonvanishing for any specific zeta value, nor an exponential multiplier, nor the weight-five irrationality measure.

### Required exact gate before merging

Integrated `lake build` PASS; `lake env lean Zetahyperbolic/Audit.lean` PASS; no `sorryAx`, extra axioms, or admitted source. Check transitive axiom sets of the seven printed declarations against `propext`, `Classical.choice`, `Quot.sound`. Freeze the four passed source files and preserve the existing project cache.

## Verified destination receipt (FROZEN)

- `P04_03_COMPLEX_PADIC_ZERO_FREE_DISK=PROVED_IN_DESTINATION_LEAN`
- Branch proof head: `19747fdced7c4e87f2e9312ca8deff8b14111525`.
- Integrated Lean build: [GitHub Actions 40259783326](https://github.com/randogelist/snditeration/actions/runs/40259783326), **PASS**, 8,765 jobs.
- Target: `Zetahyperbolic.Section4.ActualPrimitivePadicDisk`; [PR #17](https://github.com/randogelist/snditeration/pull/17) **merged**, main merge commit `1e7d422cc81c30179275707750f5fde38af5e503`.
- `#print axioms`: seven checked declarations, all exactly `[propext, Classical.choice, Quot.sound]`.
- Source placeholder scan: **PASS**. No sorry/admit declarations; no newly introduced custom axioms.
- Imported proof bodies: three companion Lean sources `zetahyperbolic-axiom@86ca99a`, original namespace preserved, import paths alone adjusted; independent byte-equivalence audit PASS.
- **PASS-ONCE:** four compiled Lean source modules frozen by this proof head and pinned toolchain/Mathlib. No `.olean` package was uploaded to GitHub by this documentation commit.
- **Scope:** exact printed Proposition 4.3 plus actual primitive-polynomial specialization under explicit p-adic center-nonvanishing hypothesis. This does **not** discharge the K=30n weight-five decay/multiplier.
