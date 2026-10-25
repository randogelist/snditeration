# Literal Section 3 claims requiring correction

These findings concern the manuscript dated 21 October 2026. They do not
invalidate the independently proved hyperbolicity and positive Gram theorems.
The Lean proof ledger must distinguish a corrected statement from the printed
statement.

## Corollary 3.5: continued fraction

For `t = X - ζ(s)`, the proof uses the resolvent `(I + t T)⁻¹`. Its finite
continued fraction has diagonal entries `1 + t*a_i` and numerators
`t²*b_i²` (with the ordering determined by the chosen endpoint vector).
The displayed `a_i + t` and `b_i²` instead belong to `(T + t I)⁻¹`.
Converting the normalized determinant ratio to `Δ_{h-1}/Δ_h` also requires
the factor `det(G_{h-1})/det(G_h)`.

The exact admissible rank-one case `(k,m,N,K) = (1,1,1,2)` has
`Δ(X) = 29/2 - 12 X`. Write `g = Δ(ζ(3)) > 0`. The printed formula at the
center equates `1/g` with `1/(-12/g)`, whose signs differ.
`Section3/ContinuedFractionObstruction.lean` checks the concrete algebra and
the sign obstruction. The correct rank-one expression is
`1/(g - 12t) = (1/g)/(1 + t*(-12/g))`.

Strict positivity of every Lanczos off-diagonal additionally requires a cyclic
starting vector (no early breakdown). Distinct eigenvalues alone do not ensure
that an arbitrary starting vector has a nonzero component in every eigenspace.
A rational ratio at `X=0` also needs `Δ_h(0) ≠ 0`.

## Corollary 3.6: finite support and the direction of the bound

The even reciprocal-root sums are moments of a positive measure with finitely
many atoms. Its Hankel matrices are positive semidefinite, and determinants
vanish when the matrix size exceeds the number of distinct squared reciprocal
root distances. Strict positivity at all orders is impossible. Distinct roots
can already give equal squared distances: roots `-1,1` with shift zero give
all even sums equal to `2` and a zero `2 × 2` Hankel determinant.

For the actual rank-one pencil above, the single root is `29/24`. At the
allowed rational shift zero, the reciprocal-square atom is `(24/29)²` and
its size-two Hankel determinant is exactly zero. This finite counterexample
is included in `ContinuedFractionObstruction.lean`.

The corrected estimate, also appearing in the manuscript's own proof, is

`h^(-1/(2r)) ≤ S_(2r)^(-1/(2r)) / d_min ≤ 1`.

The displayed statement reverses this direction. For odd `m`, its logarithmic
derivative convention also has a sign mismatch: the displayed prefactor gives
`Σ (q₀-r_j)^(-m)`, not `Σ (r_j-q₀)^(-m)`. This does not affect the even sums.

## Theorem 3.7: coefficient nonvanishing is a separate claim

Distinct nonzero real spectral values do not imply that every intermediate
shifted coefficient is nonzero. Values `β=(-1,1)` give the shifted polynomial
`1-Y²`, whose middle coefficient is zero. Nevertheless its normalized Newton
inequality is strict (`0 > -1`). The manuscript's appeal to a generically
distinct Hankel spectrum therefore does not prove its claimed coefficient
nonvanishing. This observation is not a refutation of normalized Newton
inequalities themselves; their precise hypotheses and equality cases need
independent proofs.
