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
