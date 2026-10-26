# Frozen independent target P04.02: algebraic resultant/height transfer

Owner: integration-only `integrate/pr15-p04-02-algebraic-height-v1`, based on `49379aaaa927b86e238414173aabd8396ab019d7`.
Immutable donor: `snditeration PR #15 @0cee4ea2e32b1f476488f92b476c4eb224285160`. Its overall CI failed elsewhere, but **all seven** source modules in this chain individually built in [the donor run](https://github.com/randogelist/snditeration/actions/runs/40188938699); they are copied byte-identically into this branch.

Modules: `Resultant → ConjugateBounds → AlgebraicBudget → AlgebraicTransfer → AlgebraicLimsup → AlgebraicLattice → AlgebraicHeight`. Dependencies are the existing `Transfer`, `ComparisonRadius`, `IndexSelection`, `ComplexComparison`, and pinned Mathlib on current `main`.

Exact scope: a conditional degree-`d` algebraic approximation/height transfer from an actual integer-polynomial family with explicitly assumed quadratic evaluation decay, complex-root separation, degree bounds and a height-limsup bound. `AlgebraicHeight` gives the integer minimal-polynomial wrapper for algebraic `α : ℂ`. This port does **not** prove these rate hypotheses for the paper's original ζ(5) family, nor any unconditional irrationality measure.

Review and merge gate: fresh Lean 4.33 full build, ten `#print axioms` reports on declared exact theorems, placeholder check, source byte-identity, mergeability and SHA-leased merge; subsequent `main` CI check. Do not edit the other agent's 3.3, 3.4, 3.8, 5.1, 5.2, 6.9, 6.10, or 6.16 draft branches. No other mathematical target is included.