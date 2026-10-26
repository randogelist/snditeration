# P05_04_EVEN_POLE_CANCELLATION — frozen execution target

Workflow: YOU_ARE_GOODWORKFLOWFRONTIER / A_TIER_EXECUTION
Starting `main` commit: 1c7f2f981097d01620df53b82559dd3352c97bd0
Target: original Theorem 5.4 (even pole pair cancellation).
Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.

## Exact theorem
For all k and j≥1, the actual rational integer-pole functional satisfies
τ_k((X−j)⁻¹−(X+j)⁻¹)=C(j⁻(2k+1)).
The rational functions are elements of the actual destination integer-pole domain, not an unrelated abstract rational-polynomial surrogate.
At j=1, the exact value is C(1).
The proof uses tauPolePoly_reflect, tau_difference_pole and the existing functional's pole-evaluation theorem. The source's incorrect intermediate division sign is not assumed.

## Admission gate
PASS an integrated GitHub Lean build, `#print axioms` for all four declarations with only standard axioms, and the proof-placeholder scanner.
Freeze code and commit the receipt after merge. No source in the previous PASS-ONCE closure may be changed.
No effect on ζ5/ζ7 irrationality, RH, or the infinite Krein cone claims.

## Compiler-verified receipt — FROZEN A-TIER

- Result: `P05_04_EVEN_POLE_CANCELLATION=PROVED_IN_DESTINATION_LEAN`
- PR: [#21](https://github.com/randogelist/snditeration/pull/21), **merged** as `f64b49b9b51b43626abbf09d1cf3821b187ea8b5`.
- Final verified PR source head: `7718761f994929ea81c29e1114e804f2f126f927`.
- CI: [40265986335](https://github.com/randogelist/snditeration/actions/runs/40265986335), **PASS**, 8,773 build jobs.
- Global transitive dependency audit: **PASS**, 1,011 theorem declarations reviewed in the project namespace.
- Four target declarations: `evenPolePair_coe`, `evenPolePair_cancellation`, `evenPolePair_one`, `finite_evenPolePair_cancellation`; every printed dependency set was exactly `[propext, Classical.choice, Quot.sound]`.
- Placeholder scanner: **PASS**. No `sorry`, `admit` or bare project `axiom` was introduced.
- The proof is over the *actual destination integer-pole rational-function domain* and existing `Tau.rationalFunctional`.
- PASS-ONCE frozen module: `Zetahyperbolic/Section5/EvenPoleCancellation.lean`. Previous verified code and imported Mathlib artifacts are unchanged.
- **Scope:** Theorem 5.4 is unconditional for each `k` and `j≥1`, including `j=1`. No 5.1 two-variable integral, ζ(7) irrationality, or 6.3 Krein positive cone is inferred.
