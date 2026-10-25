# Manuscript-to-Lean ledger — YOU_ARE_GOODWORKFLOWFRONTIER

Mode: `A_TIER_EXECUTION`. Checkpoint name: `ZETA_HYPERBOLIC_ANCHOR_7`.
Compiler: Lean 4.33.0. Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Manuscript: supplied 52-page version dated 21 October 2026.

## Verified baseline

PR [#13](https://github.com/randogelist/snditeration/pull/13) merged as
`6bdc42388f46669e15e0ad32d7c4e081a6bad38c` after build and axiom audit
[run 40185519251](https://github.com/randogelist/snditeration/actions/runs/40185519251)
on source head `5e05b9b80493e9abd04bb793f7c45f4fb6aa360c`.
The guard checked **717 theorem declarations** (including generated declarations),
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
This count is not a count of manuscript theorems. The earlier 600-declaration
PR #12 receipt remains preserved and its merged main CI also passed.

All earlier `.lean` files and historical ZIP archives are preserved. Reuse is
by Lake source/dependency traces and the pinned toolchain, not by filenames.
Linux/GitHub verification is recorded as such; no new native Windows receipt
is inferred from it. The axiom guard was also tested to reject a theorem
transitively using a deliberately introduced custom axiom in a temporary test.

| Manuscript item | Verified source and scope | Remaining boundary |
| --- | --- | --- |
| Definition 2.1 | `Section2/Moments.lean`, `RationalDomain.lean`, `RationalFunctionals.lean`: actual rational pencil; injective simple-pole representation and representation-independent linear functionals on RatFunc subspaces. | No arbitrary representation-invariance premise. |
| Lemma 2.2 | `Section2/TauGenerators.lean`: every polynomial pullback plus exact pole-generator values; `RationalPullbackAssembly.lean` proves full actual rational substitution and functional compatibility. | None for the full simple-square-pole domain identity. |
| Lemma 2.3 | `Section2/TauGenerators.lean`: full polynomial reflection; pole reflection; difference for every integer r ≠ 0; `RationalReflection.lean` proves full-domain actual rational reflection. | Full rational finite-difference and intrinsic coefficient identity is the next extension. |
| Theorem 2.4 | `Section2/BasisInvariance.lean`, `PoleDiagonalization.lean`: determinant congruence, constructed primitive normalization, concrete basis invariance. | Nonzero determinant is proved, not an open input. |
| Theorem 2.5 | `Section2/PoleDiagonalization.lean`: actual residues, Vandermonde factorization, nonzero diagonal slope, transformed pencil and exact degree. | Explicit interpolation-polynomial identification with the printed Lagrange functions remains separate. |
| Equation (3.2), actual pencil | `Section3/ConcreteMomentMeasure.lean`, `RationalIntegralBridge.lean`: integrability, nonzero atomless positive measure and actual original-weight integral identity. | `RationalMomentFunctional.lean` proves integrability and the exact integral identity for every rational function in the actual domain, with actual RatFunc evaluation on t≥0. |
| Theorem 3.1 | `Section3/Unconditional.lean`: actual Gram positivity, degree h, real roots avoiding ζ(2k+1), and exact positive zero-free radius attained by a root. Only structural `Admissible` hypotheses remain. | `ActualSpectrum.lean` constructs B=(sqrt G)⁻¹M(sqrt G)⁻¹, identifies its actual eigenvalues and ℓ² operator norm, and proves the sharp radius 1/‖B‖₂ with boundary attainment. Pairwise distinct roots are not asserted. |
| Primitive polynomial (2.9) | `Section3/PrimitivePolynomial.lean`: constructed primitive integer polynomial, same degree and complex zero set, inherited exact zero-free disk. | None for these precise declarations. |
| Proposition 3.2 | Printed continuous-density normalization differs by π/2 at odd weights. | Repair before proving coincidence with (2.8); see correction notes. |
| Theorem 3.3(1) | Positive definiteness of the actual Hankel Gram is proved. | Strict total positivity of arbitrary mixed minors and Stieltjes determinacy/Carleman are open. |
| Theorem 3.3(2) | `Section3/PoleSigns.lean`: primitive weight-five leading sign is (-1)^(n(n-1)/2). | None for this exact sign statement. |
| Theorem 3.3(3) | `Section3/PoleSigns.lean`: actual γ_a has sign (-1)^(a-1), exact parity criteria and general leading sign. | Sylvester inertia and actual eigenvalue/root-side count transfer remain open. |
| Theorem 3.4 | General principal-minor real-rootedness candidates identified in archives. | Not imported yet; full Cauchy interlacing/Dodgson connection remains open. |
| Corollaries 3.5–3.6 | `Section3/ContinuedFractionObstruction.lean`: actual rank-one determinant/root, finite-moment Hankel singularity and corrected scalar resolvent algebra. | `ContinuedFractionCounterexample.lean` proves the actual admissible positive-center counterexample. Literal printed claims require correction. |
| Theorem 3.7 | Distinct real factors do not imply nonzero intermediate coefficients; exact example is checked. | Precise Newton/Turán statements and equality cases require separate proofs. |
| Theorem 4.1 | `Section4/Transfer.lean`: audited conditional arithmetic transfer to a quantitative rational measure and irrationality. | Concrete growth/decay/comparison/index-budget hypotheses remain open. |
| Sections 4–6 applications | Archive candidates retained; see source frontier. | No unconditional ζ(5), ζ(7), or linear-form irrationality asserted. |

## Continuation policy

Use [ARCHIVE_FRONTIER.md](ARCHIVE_FRONTIER.md) for exact reusable source locations.
The current open extension work is confined to new modules, preserving the
verified baseline. The next compile/audit receipt must distinguish these
extensions from the previously verified 717 declarations.

[MANUSCRIPT_REPAIRS.md](MANUSCRIPT_REPAIRS.md) and
[SECTION3_CORRECTIONS.md](SECTION3_CORRECTIONS.md) record exact corrections.
A proof of a corrected formula is not a proof of the original false formula.
No RH, S-Tier finite-witness admission, or full manuscript closure is claimed.

## Candidate extension (not yet integrated)

LagrangeBasis, TauPolynomialDifference, RationalDifference and PrincipalPencils
have passed local Lean checks. PoleSignCounts and SpectralInertia are new
construction modules. The next CI snapshot imports and audits all six.
No candidate is promoted to the verified table before its integrated receipt.
