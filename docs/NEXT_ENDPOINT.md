# Next unfinished endpoint

## Lemma 2.3: identify the canonical coefficient with the analytic derivative

The algebraic finite-difference theorem is `Tau.rationalFunctional_difference`
in `Section2/RationalDifference.lean`. The remaining bridge is an equality in ℝ:

```
(partialFractionCoefficient (2*k) f : ℝ)
  = iteratedDeriv (2*k)
      (fun x => RatFunc.eval (Rat.castHom ℝ) x (f : RatFunc ℚ)) 0
      / ((2*k).factorial : ℝ)
```

Require `(RatFunc.denom (f : RatFunc ℚ)).eval 0 ≠ 0`. This is proved for the
square-pole domain by `Mu.rationalDomain_regular_at_zero`; on the integer-pole
domain, `Tau.eval_denom_zero_ne_zero` supplies it when the coefficient of the
pole at zero vanishes. Do not replace this with differentiability of a
rational function that has a pole at the origin.

Use the unique coordinates from `SimplePole.coordinates`. Prove the analytic
identity for a polynomial and each supported nonzero simple pole, then use
finite-sum linearity and regularity to identify the resulting function with
actual `RatFunc.eval` in a neighborhood of zero. Existing algebraic difference
and regularity modules are frozen starting points; add a new bridge module.

## Larger manuscript endpoints still open

- Theorem 3.3(1): strict positivity of arbitrary mixed Hankel minors, plus
  moment growth and Carleman/Stieltjes determinacy. Principal positivity alone
  does not prove total positivity.
- Theorem 3.4: compatible compressions and full Cauchy interlacing, and the
  arbitrary-order Dodgson/Jacobi connection. Principal-root reality allows
  degree loss and does not prove interlacing.
- Theorem 3.7: precise Newton/Turán inequalities and equality cases. Distinct
  real roots do not force every intermediate coefficient to be nonzero.
- Sections 4–6: concrete growth, decay, comparison and index-budget premises
  for the audited arithmetic transfer. No unconditional irrationality of
  ζ(5) or ζ(7), RH, or full-manuscript closure has been established.

Printed Proposition 3.2 and Corollaries 3.5–3.6 require the repairs recorded in
`MANUSCRIPT_REPAIRS.md` and `SECTION3_CORRECTIONS.md`. Preserve the proven
counterexamples and corrected bounds rather than trying to prove the false
printed statements unchanged.
