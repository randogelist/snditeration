# Manuscript repairs and proof boundaries

These notes concern the supplied 52-page manuscript dated 21 October 2026.
They separate errors in printed arguments or formulas from verified Lean
statements. The general hyperbolicity argument of Theorem 3.1 is unaffected.

## Lemma 2.3 — Bernoulli reflection proof

The text incorrectly claims that only odd monomial degrees contribute.
The Bernoulli index-one case (degree 2k) contributes and must be treated
separately. It also says even Bernoulli indices greater than one vanish;
the vanishing parity is odd. `Section2/TauGenerators.lean` proves the
reflection identity with the exceptional case handled explicitly.
The pole difference identity is proved for every integer r ≠ 0, which
also includes the manuscript's stated r ∉ {0,1} range.

## Proposition 3.2 — continuous normalization

At s=2k+1, the printed continuous prefactor is π/2 times the odd-weight
prefactor in (3.1). Replace it by `2(2π)^(s-1)/Γ(s)` before asserting the
continuous pencil coincides with (2.8). Positivity of the differently
normalized pencil does not itself prove that equality.

## Corollary 3.5 — continued-fraction normalization

For a tridiagonal T with diagonal a_i and adjacent entries b_i, the
resolvent `(I + t T)⁻¹` has continued-fraction denominators `1 + t a_i`
and numerators `t² b_i²`. The printed expression instead uses `a_i + t`
and `b_i²`, corresponding to a different resolvent. Converting normalized
principal determinants to the original Δ-ratio also requires the factor
`det(G_{h-1}) / det(G_h)`.

The claimed strict positivity of every Lanczos coefficient needs an
appropriate cyclic-vector or no-breakdown argument. Distinct eigenvalues
alone do not ensure it for an arbitrary starting vector. The manuscript's
Theorem 3.1 does not assert that all roots are pairwise distinct.

An exact rank-one algebraic instance is checked in
`Section3/ContinuedFractionObstruction.lean`; its audit status is recorded
in the ledger. Do not promote the printed Corollary 3.5 as proved.

## Corollary 3.6 — finite-support moments

A measure supported on h points cannot have strictly positive Hankel
determinants of all orders: rank is at most h. Repeated squared root
distances can lower the rank further. For roots −1 and 1 about q=0,
every even reciprocal-root sum is 2, so even the 2×2 moment determinant
is zero.

The proof gives the correct approximation bounds
`h^(-1/(2r)) d_min ≤ S_(2r)^(-1/(2r)) ≤ d_min`; the displayed statement
reverses the normalized inequalities. For odd m, the logarithmic-derivative
formula has an additional sign issue: the stated derivative prefactor yields
`Σ(q-r_j)^(-m)`, not `Σ(r_j-q)^(-m)`. Even moments are unaffected.

## Theorem 3.7 — genericity is not coefficient nonvanishing

Distinct real spectral values do not imply every intermediate coefficient
is nonzero: β=(-1,1) gives `1-Y²`. This invalidates that justification and
the associated universal coefficient-nonvanishing assertion. It does not
by itself refute every Newton inequality stated in the theorem.

## Unfinished arithmetic endpoints

Theorem 4.1's compiled transfer theorem retains explicit growth, decay,
comparison and index-budget hypotheses. No proof of those hypotheses for
the actual ζ(5)/ζ(7) family is supplied by the spectral theorem or by an
archive filename. Irrationality and finite-witness closure remain open.
