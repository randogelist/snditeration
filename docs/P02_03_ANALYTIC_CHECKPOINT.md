# P02.03 — normalized analytic derivative (FROZEN)

Workflow: YOU_ARE_GOODWORKFLOWFRONTIER, A_TIER_EXECUTION.
Original item: Lemma 2.3, original 52-page Zetahyperbolic manuscript.
Compiler: Lean 4.33.0 with Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Base main: 6622c8e6bbfd6f88a7db908fc7ea0a52c16a42fc.

## Verified destination result

The true polynomial Taylor coefficient is the normalized analytic
iterated derivative, as is each finite simple-pole coefficient away
from the pole. Via the injective rational-coordinate representation,
the exact finite-difference functional of every element of
ManuscriptChain.Tau.RationalDomain with zero residue at pole zero equals
the normalized real analytic derivative of its canonical real realization.

Main theorem:
`ManuscriptChain.Tau.rationalFunctional_difference_analytic`
Auxiliary:
`normalized_derivative_rationalDomain`,
`rationalDomain_coefficient_eq_coordinate_derivative`,
`polynomialReal_normalized_derivative`,
`poleElement_coefficient_eq_analytic`.

Files:
- `Zetahyperbolic/Section2/AnalyticDerivative.lean`
- `Zetahyperbolic/Section2/PolynomialDerivative.lean`
- `Zetahyperbolic/Section2/RationalAnalyticBridge.lean`

## Verified source/compiler receipt

- PR: https://github.com/randogelist/snditeration/pull/18
- Proof source head: d6c79fdeca8f77928a934acecf1b7af96fdb6fee
- Green Actions run: https://github.com/randogelist/snditeration/actions/runs/40262441761
- Build: 8,768 jobs PASS, root library, targeted audit, placeholder scan all PASS.
- 10 targeted declarations: transitive axioms only propext, Classical.choice, Quot.sound.
- Squash merge: c935c9963608a1ab3b58fe9af4c849dd4b47d3d4.
- The three proof-module Git blobs at merge are immutable for PASS-ONCE
  unless their sources, compiler, Mathlib or transitive dependencies change.
- Verification environment: GitHub Actions Linux. No native Windows
  compilation receipt is inferred from this run.

## Explicit semantic boundary

The theorem defines the real analytic evaluation through the UNIQUE
polynomial-plus-simple-pole coordinates of the true rational-function domain.
It does NOT prove equality of that evaluation with Mathlib's totalized
`RatFunc.eval` at arbitrary real points in a neighborhood of zero.
That compatibility statement remains a separately registered optional
formalization bridge. Zero-residue regularity at the origin is an
explicit hypothesis and is not erased.

## Next target

Theorem 5.4: exact even-pole-pair cancellation. Already certified in the
companion repository; a new local import/adapter branch has NOT been started.
