# Next single-target handoff

## Target frozen for next execution: Theorem 5.4 — even-pole cancellation

As of P02.03 / PR #18, Lemma 2.3's normalized analytic derivative and actual
rational-domain finite difference are A-Tier verified in the canonical
unique polynomial/pole-coordinate realization. Existing Section2 source
files and new proof modules remain PASS-ONCE frozen.

The companion `zetahyperbolic-axiom@86ca99a` already compiled
`LeanPaper.Section2TauLinear.evenPolePair_cancellation`
for every integer j≥1, including the j=1 exception.

## Required P05.04 destination tasks (not started)

1. Use the canonical `Tau.rationalFunctional` and actual `RatFunc`
   domain objects already in `snditeration/main`.
2. Express the even pole pair `(x-j)⁻¹-(x+j)⁻¹` for each j≥1 in
   the correct integer-pole domain.
3. Prove the exact theorem value `j^(-(2k+1))` for the paper's
   normalization and weight convention, including j=1.
4. Print the exact axiom dependencies, run full Lean 4.33 GitHub
   CI and merge only after PASS; do not transfer the upstream
   theorem name without proving equality of actual domain objects.
5. Keep previous source/olean artifacts untouched under PASS-ONCE.

## Separate optional technical bridge — NOT certified by P02.03

For any regular domain element `f`, prove on an open neighborhood of zero
that the canonical `Tau.analyticRealization f` agrees pointwise with
Mathlib's `RatFunc.eval (Rat.castHom ℝ) x (f : RatFunc ℚ)`,
and transport `iteratedDeriv` along that eventual equality.
The printed finite-pole/span analytic derivative statement and its
canonical rational-domain form are already proved; this strengthens
interoperability with Mathlib's totalized evaluation API. Do not treat
this optional bridge as a theorem that the previous CI checked.

No ζ5/ζ7 irrationality or RH result is asserted.
