# Frozen P05.01 — rationality completion of printed two-variable ζ(7) moments

Theorem 5.1 at original paper equations (5.1)–(5.2), PDF pp. 22–23.

The actual integral density and all its diagonal/off-diagonal identities are
already proved in `BeukersMomentSeries.lean`, `BeukersOffDiagonal.lean`, and
`BeukersDensity.lean`, imported into `main` via PR #24 after CI
[40267850777](https://github.com/randogelist/snditeration/actions/runs/40267850777)
(8,783 build jobs; standard-only transitive proof audit).

This follow-up proves the *explicit rationality* assertion:
for r≠t, the off-diagonal integral is the image in ℝ of the concrete
harmonic divided difference
`(H_r^(6)-H_t^(6))/(6*(r-t)) : ℚ`.

The only edited source module is `Section5/BeukersRationalMoments.lean`.
Dependencies and previously passed source artifacts are untouched.
To finalize: integrated `lake build`, transitive `#print axioms` for
`offdiagonal_moment_eq_rat` and `offdiagonal_moment_is_rational`,
placeholder scanner, and exact source/receipt confirmation.

No zeta(7) irrationality, infinite Krein cone, or p-adic approximation
certificate is inferred.
