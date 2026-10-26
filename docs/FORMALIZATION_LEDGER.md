# Manuscript-to-Lean ledger — YOU_ARE_GOODWORKFLOWFRONTIER

Mode: `A_TIER_EXECUTION`. Checkpoint name: `ZETA_HYPERBOLIC_ANCHOR_7`.
Compiler: Lean 4.33.0. Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Manuscript: supplied 52-page version dated 21 October 2026.

## Verified baseline

PR [#14](https://github.com/randogelist/snditeration/pull/14) merged as
`1460d455583ffbe5e08bbcb3274f9002be36b5ef` after build and axiom audit
[run 40186462123](https://github.com/randogelist/snditeration/actions/runs/40186462123)
on source head `351f704e8a6b3b942e12c67f5213c011b970af16`.
The guard checked **846 theorem declarations** (including generated declarations),
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
This count is not a count of manuscript theorems. Earlier PR #12 (600) and
PR #13 (717) receipts remain preserved with exact build/audit log excerpts.

All earlier `.lean` files and historical ZIP archives are preserved. Reuse is
by Lake source/dependency traces and the pinned toolchain, not by filenames.
Linux/GitHub verification is recorded as such; no new native Windows receipt
is inferred from it. The axiom guard was also tested to reject a theorem
transitively using a deliberately introduced custom axiom in a temporary test.

| Manuscript item | Verified source and scope | Remaining boundary |
| --- | --- | --- |
| Definition 2.1 | `Section2/Moments.lean`, `RationalDomain.lean`, `RationalFunctionals.lean`: actual rational pencil; injective simple-pole representation and representation-independent linear functionals on RatFunc subspaces. | No arbitrary representation-invariance premise. |
| Lemma 2.2 | `Section2/TauGenerators.lean`: every polynomial pullback plus exact pole-generator values; `RationalPullbackAssembly.lean` proves full actual rational substitution and functional compatibility. | None for the full simple-square-pole domain identity. |
| Lemma 2.3 | `Section2/TauGenerators.lean`: full polynomial reflection; pole reflection; difference for every integer r ≠ 0; `RationalReflection.lean` proves full-domain actual rational reflection. `TauPolynomialDifference.lean` and `RationalDifference.lean` prove the full finite-difference identity with a canonical partial-fraction coefficient. | Identification with the normalized analytic derivative remains open; regularity is proved in `RationalRegularity.lean`. |
| Theorem 2.4 | `Section2/BasisInvariance.lean`, `PoleDiagonalization.lean`: determinant congruence, constructed primitive normalization, concrete basis invariance. | Nonzero determinant is proved, not an open input. |
| Theorem 2.5 | `Section2/PoleDiagonalization.lean`: actual residues, Vandermonde factorization, nonzero diagonal slope, transformed pencil and exact degree. `Section2/LagrangeBasis.lean` gives the printed product, interpolation values, degree, inverse-Vandermonde coefficients and the exact change-of-basis identification. | None for these precise declarations. |
| Equation (3.2), actual pencil | `Section3/ConcreteMomentMeasure.lean`, `RationalIntegralBridge.lean`: integrability, nonzero atomless positive measure and actual original-weight integral identity. `RationalMomentFunctional.lean` proves integrability and the exact integral identity for every rational function in the actual domain, with actual RatFunc evaluation on t≥0. | None for the odd-weight rational-domain integral theorem (k>0). |
| Theorem 3.1 | `Section3/Unconditional.lean`: actual Gram positivity, degree h, real roots avoiding ζ(2k+1), and exact positive zero-free radius attained by a root. Only structural `Admissible` hypotheses remain. `ActualSpectrum.lean` constructs B=(sqrt G)⁻¹M(sqrt G)⁻¹, identifies its actual eigenvalues and ℓ² operator norm, and proves the sharp radius 1/‖B‖₂ with boundary attainment. | Pairwise distinct roots are not asserted. |
| Primitive polynomial (2.9) | `Section3/PrimitivePolynomial.lean`: constructed primitive integer polynomial, same degree and complex zero set, inherited exact zero-free disk. | None for these precise declarations. |
| Proposition 3.2 | Printed continuous-density normalization differs by π/2 at odd weights. | Repair before proving coincidence with (2.8); see correction notes. |
| Theorem 3.3(1) | Positive definiteness of the actual Hankel Gram is proved. | Strict total positivity of arbitrary mixed minors and Stieltjes determinacy/Carleman are open. |
| Theorem 3.3(2) | `Section3/PoleSigns.lean`: primitive weight-five leading sign is (-1)^(n(n-1)/2). | None for this exact sign statement. |
| Theorem 3.3(3) | `Section3/PoleSigns.lean`: actual γ_a has sign (-1)^(a-1), exact parity criteria and general leading sign. `SpectralInertia.lean` proves Sylvester transfer, exact eigenvalue/root-side counts with spectral multiplicities, and weight-five floor(27n/2) below / ceil(27n/2) above ζ(5). `PoleSignCounts.lean` evaluates the parity counts. | Counts retain spectral multiplicities; root simplicity is not asserted. |
| Theorem 3.4 | `Section3/PrincipalPencils.lean` proves actual injective principal-base positivity, nonzero principal determinant polynomials and reality of all their complex roots, with exact identification of the rational principal determinant. | Singular principal directions and degree loss are allowed; full Cauchy interlacing/Dodgson connection remains open. |
| Corollaries 3.5–3.6 | `Section3/ContinuedFractionObstruction.lean`: actual rank-one determinant/root, finite-moment Hankel singularity and corrected scalar resolvent algebra. `ContinuedFractionCounterexample.lean` proves the actual admissible positive-center counterexample. `ReciprocalMoments.lean` and `ReciprocalMomentLimit.lean` prove the corrected estimate bounds and convergence to 1/‖B‖₂. | Literal printed claims require correction. A general corrected Lanczos continued-fraction theorem remains separate. |
| Theorem 3.7 | Distinct real factors do not imply nonzero intermediate coefficients; exact example is checked. | Precise Newton/Turán statements and equality cases require separate proofs. |
| Theorem 4.1 | `Section4/Transfer.lean`: audited conditional arithmetic transfer to a quantitative rational measure and irrationality. | Concrete growth/decay/comparison/index-budget hypotheses remain open. |
| Proposition 4.3 | `Section4/{PadicDisk,IsometricExtension,ComplexPadicDisk,ActualPrimitivePadicDisk}.lean`: exact ℂ_p norm-preserving zero-free disk for every integer polynomial with nonzero value at an integral p-adic center, plus the true manuscript primitive Hankel polynomial specialization. **A-Tier destination Lean 4.33 PASS**: [PR #17](https://github.com/randogelist/snditeration/pull/17), [CI 40259783326](https://github.com/randogelist/snditeration/actions/runs/40259783326), merged `1e7d422cc81c30179275707750f5fde38af5e503`. All seven printed axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`; 8765 build jobs/placeholder scanner PASS. | Center nonvanishing for a **specific p-adic zeta value** is not supplied. No weight-five multiplier, K-uniform estimate or ζ(5) irrationality follows from the disk theorem alone. |
| Sections 4–6 applications | Archive candidates retained; see source frontier. | No unconditional ζ(5), ζ(7), or linear-form irrationality asserted. |

## Continuation policy

Use [ARCHIVE_FRONTIER.md](ARCHIVE_FRONTIER.md) for exact reusable source locations.
The verified source is frozen at the receipt above. Continue in new modules
from [NEXT_ENDPOINT.md](NEXT_ENDPOINT.md), beginning with the normalized
analytic-derivative bridge for Lemma 2.3. Do not weaken a statement or insert
a missing conclusion as an unexplained premise.

[MANUSCRIPT_REPAIRS.md](MANUSCRIPT_REPAIRS.md) and
[SECTION3_CORRECTIONS.md](SECTION3_CORRECTIONS.md) record exact corrections.
A proof of a corrected formula is not a proof of the original false formula.
No RH, S-Tier finite-witness admission, or full manuscript closure is claimed.

## Checkpoint status

All imported proof modules in this checkpoint passed the integrated build and
allowlist audit. There are no unfinished construction modules in the import
closure. Open mathematics is recorded in NEXT_ENDPOINT.md, not represented
by placeholders or custom axioms.
