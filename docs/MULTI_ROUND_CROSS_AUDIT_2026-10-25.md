# Repeated cross-branch manuscript proof audit — 2026-10-25

**Scope:** Four independent inspection rounds of the *original* 52-page PDF, `snditeration` GitHub, `zetahyperbolic-axiom` GitHub, and the supplied historical Lean ZIPs. This is a **source-verified gap tracker**, not a new Lean compilation. It augments, without weakening, [the 45-item master tracker](PAPER_GAP_TRACKER.md) and [64-subclaim register](PAPER_GAP_REGISTER.md).

## 1. Canonical proof-tier definitions (established workflow v1_0_15)

| Marker | Tier | Evidence |
|---|---|---|
| `!` | **B-Tier** | Defensible on-paper derivation; not yet Lean verified |
| `!!` | **A-Tier** | Exact Lean theorem compiled and transitively axiom-audited; no `sorryAx`, extra axioms or unstated hypotheses |
| `!!!` | **Formal closure** | A-Tier proof reduces final target to a terminating finite-witness checker, but accepted witness is outstanding |
| `!!!!` | **S-Tier** | Concrete finite raw-data witness actually passes checker, with audited Lean transfer proving the target |

Only an exact *statement* earns a tier. Cross-repo proof status, source integration, literal manuscript equivalence, corrected replacement and partial coverage are **different axes**. In particular, `!!` on a conditional transfer does **not** discharge its mathematical premises.

## 2. Round A — local `snditeration` frozen checkpoint

**Baseline:** `snditeration/main@c521749190cce9981b0f108a8edc8034420f6420`, [CI PASS 40186793090](https://github.com/randogelist/snditeration/actions/runs/40186793090), [CHECKPOINT](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/CHECKPOINT.json): 846 audited theorem declarations (including generated declarations), Lean 4.33.0, pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

Exact complete printed item closures in the local code: **2.2, 2.4, 2.5, 3.1**. Other locally verified *proper* results: 3.3 leading sign, actual Sylvester inertia, multiplicity-counted root-side counts, reality of principal minors with singular slopes and degree loss, corrected reciprocal-root limit, positive integral realization and conditional integer-polynomial irrationality transfer. These proper subclaims do not complete §§3.3, 3.4, 3.6 or 4.1 as printed.

The new 51-file [PR #15](https://github.com/randogelist/snditeration/pull/15), head `0cee4ea2e32b1f476488f92b476c4eb224285160`, is **CI FAILED** ([run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699)); its build failures include `LaplaceWeightDerivative`, `BeukersMomentSeries`, `MatrixCurveJacobi`, `ContinuousPencil`, `CauchyInterlacing`, `ChristoffelDarboux`, `PrincipalCondensation`, `RationalIndependence`, `CoefficientGramGrowth`. No new `snditeration/main` A-Tier claims are based on it.

## 3. Round B — companion `zetahyperbolic-axiom` exact Lean declarations

**Baseline:** [main@86ca99a23d65cde4880a9005a49076c43e7bc968](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968), [CI PASS 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869), [219-module acceptance](https://github.com/randogelist/zetahyperbolic-axiom/blob/main/validation/linux/acceptance.json) and [transitive axiom audit](https://github.com/randogelist/zetahyperbolic-axiom/blob/main/validation/linux/proof_integrity.json). This separate repo has exact complete printed proofs for **2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4**. Three items not yet imported locally can be crossed off at **aggregate** scope: 2.3, 4.3, 5.4.

Additional **genuine A-Tier subclaims** uncovered or sharpened by inspecting theorem *types* (all references under `src/LeanPaper/` at that pinned commit):

| Printed parent | Newly recognized checked subclaim / direct Lean declaration | What is **not** proved |
|---|---|---|
| **3.4(2)** | ✓ ~~All-rank actual-pencil Dodgson identity and nonpositive minor-root specialization~~: `DodgsonCondensation.manuscript_condensation`, `manuscript_at_minor_root` | Compatible rank-sensitive Cauchy root interlacing; the printed universal r-root count is invalid for singular slopes |
| **3.7(1)** | ✓ ~~All-order actual derivative Turán nonnegativity, strictness away from derivative zeros, equality criterion~~: `HigherDerivativeTuran.actual_primitive_all_derivative_turan`, `..._strict`, `..._equality` | No proof of the separate false inference “distinct roots ⇒ all centered coefficients nonzero” |
| **3.7(2)** | ✓ ~~Normalized actual coefficient Newton inequality and exact strict/non-strict coefficient criterion~~: `NormalizedNewton.actual_primitive_coefficient_newton`, `ActualStrictNewton.actual_coefficient_strict_criterion` | Does not individually certify nonvanishing of every centered coefficient |
| **3.7(3)** | ✓ ~~Actual shifted/centered weak Newton hierarchy and strict centered normalized inequality~~: `NormalizedNewton.actual_primitive_centered_newton`, `ActualStrictNewton.actual_centered_newton_strict` | The appended assertion “all intermediate centered coefficients are nonzero” remains open/unsupported |
| **3.8(1)** | ✓ ~~Actual relative matrix and negative-pole kernel share characteristic polynomial and trace~~: `ImportedSection3/ActualPoleKernel.actual_relative_charpoly_eq_pole`, `actual_relative_trace_eq_pole` | The *monic orthogonal-polynomial Christoffel–Darboux kernel* is not yet identified with this matrix |
| **3.8(2)** | ✓ ~~Finite affine-determinant/logarithmic Jacobi derivative identity~~: `ImportedSection3/Jacobi.actual_affine_log_jacobi` | Laplace-deformed actual moment measure, justified integral differentiation and full displayed integral `(3.8)` |
| **4.1** | ✓ ~~Finite index selection and conditional *explicit* threshold given a computable onset/rate certificate~~: `Section4IndexSelection`, `Section4EffectiveBudget.effective_spectral_measure` | Bare “eventually” assumptions do not produce an effectively computable onset; actual ζ(5) rates remain absent |
| **4.2** | ✓ ~~Integer resultants, conjugate bounds and the conditional degree-d algebraic approximation transfer for a polynomial root~~: `Section4Resultant`, `Section4ConjugateBounds`, `Section4AlgebraicLimsup.algebraic_transfer_limsup` | Original statement quantified directly over algebraic numbers; local minimal-polynomial wrapper and independent actual-family quantitative hypotheses remain open |
| **4.6** | ✓ ~~Finite exact leading coefficient = center value × normalized/relative determinant and its reciprocal barrier~~: `ImportedSection4/Theorem_4_6_Leading_Coefficient_Determinant_Barrier`, `ImportedSection56/FiniteDeterminant` | Family-specific positive potential-energy/determinant exponential asymptotics and height bounds |
| **4.7** | ✓ ~~Finite spectral cap + average ⇒ cluster fraction inequality; paper's 1.40% numeric *conditional arithmetic*~~: `ImportedSection4/Theorem_4_7_Finite_Root_Cluster_Count.theorem_4_7_cluster_fraction_lower_bound`, `...cluster_percentage_arithmetic` | The actual K-family upper spectral cap, lower log-determinant average and Mahler separation |
| **4.8(2)** | ✓ ~~Finite product-of-root-distance lower and upper bounds~~: `ImportedSection4/Proposition_4_8_Factor_Distance_Bounds.proposition_4_8_factor_evaluation_bounds` | Actual root/height estimates; the printed proof of 4.8(1) reverses a one-sided spectral gap (see Round D) |
| **5.1–5.2(1)** | ✓ ~~Finite dual rational moment formulas, coefficient Gram `CCᵀ` positivity, determinant degree/real spectrum~~: `ImportedSection56/DualMoments`, `PositiveSlopeSpectrum`, `DualNonsingularDegree`, `Section5DualSpectrum` | True infinite two-variable measure and Krein decomposition/tail-control |
| **5.2(3)** | ✓ ~~Finite-dimensional obstruction `2h ≤ K+1`~~: `KreinDimensionObstruction` | The literal fixed-K cone quantifier cannot hold without repair |
| **5.3** | ✓ ~~Finite β(4) two-/three-node tensor-grid positivity identities~~: `Section6BetaFinite` | Analytic β(4) two-variable measure and dual spectral identification |
| **6.2** | ✓ ~~Exact `6·d_K^7` common denominator and adjacent harmonic difference~~: `BeukersDenominator.dualConstant_seven_denominator` | Simultaneous ζ(6)/ζ(7) Beukers integral identities |
| **6.6** | ✓ ~~Anchored finite semidefinite weight cone and positive-slope spectral algebra~~: `ImportedMultiweight/AnchoredSemidefiniteCone.ANCHORED_FINITE_CONE_POSDEF` | Actual infinite multiweight density, arithmetic multipliers and universal family asymptotics |
| **6.9** | ✓ ~~Finite triple-pole Hermite local-block determinant and congruence under explicit nonvanishing hypotheses~~: `ImportedSection56/TriplePoleHermite.momentMatrix_det_ne_zero` | Family-specific Hermite basis determinant, nonzero top jet and q-adic valuation |
| **6.10(1)** | ✓ ~~Finite normalized determinant/potential identity under matrix hypotheses~~: `ImportedSection56/FiniteDeterminant.abs_leadingCoeff_eq_eval_mul_sqrt_det` | Positive limiting potential gap, reweighting strictness and quadratic growth transfer |
| **6.13** | ✓ ~~All-k finite central-factorial differential identity and positive exponential envelope~~: `CentralFactorialSecant`, `CentralFactorialDecay` | The printed series has an incorrect `(-1)^(k-1)` sign, and the infinite differentiated sum/beta pencil are unproved |
| **6.15(1)** | ✓ ~~Odd β-values = nonzero rational π-powers, qualitative transcendence and finite rational independence with 1~~: `OddBetaValues` + audited pinned `ExternalPi/` | Effective irrationality measures, all-order one-variable Gram/rank-one claims and false exterior asymptotic |
| **6.18** | ✓ ~~Explicit shifted numerator/denominator degrees and quotient-vanishing threshold~~: `DyadicQuotientThreshold` | 2-adic multipliers, valuations, dyadic height growth and effective measure |

**Interpretation:** these 20 lines are **completed subclaims, not 20 additional manuscript items**. Some were already noted in the earlier tracker but their exact closure boundaries and theorem names were not crossed off. **The exact full-item total remains 7/45.** None of these has yet been recompiled in `snditeration/main`; their `!!` status refers only to the pinned companion.

## 4. Round C — historical ZIP proof-source challenge

Read the supplied historical ZIP source inventories and explicit verification-status/README receipts, including:

- `zeta5-spectral-lean (1).zip`: 102 Lean source files, archived merged 28-module checked subset; states that its actual ζ(5) implication **requires** `MainNormalization`, `BaseValuePositive`, `MultiplierUpper` and `ArchimedeanUpper` (and the quantitative measure also needs spectral data). The compiled `theorem_4_4_irrationality_riemannZeta` is **conditional**, despite its name. Critically, the archive itself proves `denominatorClearingNormalization_no_multiplierUpper`, showing that simple positive denominator clearing fails the required rapidly decaying multiplier inequality. **Do not** cross off 4.4 from this archive.
- `Zetahyperbolic-general-assembled-lean433 (2).zip` and `(3).zip`: explicit 4.4/5.1/5.2 source modules and Lean 4.33 audit logs, but the headline zeta(5) endpoint still carries quantitative premises and the 5.1/5.2 files are not by themselves a manuscript-wide checked closure in the current repositories.
- `ZETAHYPERBOLIC_PAPER45_TEN_STAGE_LEAN_v0_1_20_FINITE_GRAM_AUDIT.zip`: finite Gram, stage audit and Section 4 transfer sources; **not** a proof that the ten-stage rate/potential endpoints hold for the manuscript family.
- `ZETA_HYPERBOLIC_PAPER10_CHAIN_FASTCORE_v0_2_16_WEIGHTED_MONOMIAL_GRAM (1).zip`: native user-reported PASS-ONCE receipts of weighted Gram/spectral/moment components. User-reported platform caches/receipts require source/dependency provenance checks and do not supersede the GitHub A-Tier proof baseline.
- `ODD_ZETA_3X3_MERGED_v0_3_0.zip`: independent odd-zeta conditional certificate architecture and weight-five transfer; no admitted concrete all-weight certificate or 4.4 actual-family rate proof.
- `ZETAHYPERBOLIC_ANCHOR_CHAIN_10_STAGES_v0_2_6_ADJACENT_DRIFT_BRIDGE1.zip`: explicitly unfinished block-rate and adjacent-drift premises; no manuscript arithmetic closure.

An uploaded archive, source filename, or old compiler log is *candidate provenance* until the original theorem statement, dependency closure and authenticated passing receipt are established in a supported environment. This round adds **reusable source targets and concrete blockers** but **zero additional whole-item crossings**.

## 5. Round D — compare literally with original manuscript

Re-read the PDF's statement/proof passages for 2.3, 3.7, 3.8, 4.2, 4.7–4.8, 5.2, 5.4, 6.3 and 6.15. The key distinctions:

1. **Lemma 2.3:** the final printed difference is required for a single admissible pole and finite span, and is **proved** in the companion as an actual iterated derivative; `snditeration`'s planned all-regular-RatFunc derivative normalization is **stronger**. It must remain open locally but must not mask aggregate 2.3 completion.
2. **Theorem 3.7:** parts (1) and (2), and the *strict normalized inequality* in part (3), have genuine audited proofs over the actual primitive family. Its extra clause asserting *every intermediate centered coefficient nonzero* remains unsupported; having at least two distinct roots does not give that coefficient statement.
3. **Proposition 4.2:** audited theorem `Section4AlgebraicLimsup.algebraic_transfer_limsup` includes degree bound, complex-root control, limsup height hypothesis and a quantified resultant-derived distance. Its hypotheses still refer to an assumed sequence of integer polynomials; the exact algebraic-number/minimal-polynomial wrapper has not passed as a single printed endpoint.
4. **Proposition 4.8(1), PDF pp. 21–22:** the manuscript invokes the **lower** bound `|r_j-ζ(5)| ≥ exp(-11.411K)` from 4.4 and then describes it as though **all** roots lie in `|r_j-ζ(5)| ≤ exp(-11.411K)`. This reverses the bound and does not justify choosing `τ=11.411` in the earlier cluster-discussion step. The generic factor-distance inequalities of 4.8(2) are valid and audited separately; the global rational-root exclusion stays **OPEN / source-proof repair**, not refuted as a theorem merely by a faulty proof.
5. **Theorem 5.2(3):** for `K=h=2`, `ℚ[x]≤K` has dimension 3 and cannot contain both disjoint 2-dimensional positive and negative definite subspaces of one symmetric bilinear form. Correct the quantifier to sufficiently large K; then *still* control the discarded infinite Krein tail.
6. **Theorem 6.3(2):** the independent exact rational `h=4` Beukers counterexample supplies a *negative* quadratic direction within the stated orthogonality kernel. This is a mathematically substantial obstruction; its rational checker + analytic enclosure **is not a Lean kernel replay**. Do not label the literal printed positivity statement A-Tier.
7. **Proposition 3.2**, **Corollaries 3.5–3.6**, **6.13** and **6.15** require the previously documented normalization, rank, factor-sign or Szegő-asymptotic repairs before literal equivalence can be claimed.

**Repeated-audit verdict:** 7 exact manuscript items crossed at A-Tier (4 local, 3 companion), substantial additional A-Tier subclaims crossed **within** 13 partially formalized/blocked parent items. No new proof of the unconditional ζ(5) irrationality exponent, ζ(7) irrationality, or S-Tier finite witness was located.

## 6. Durable actions

1. **Freeze 7 exact whole-item crossings** until the corresponding source hash/import or mathematical theorem statement changes.
2. **Promote cross-verified items locally**: 2.3, 4.3, 5.4; also import the already audited Dodgson and corrected 3.6 package and the strict 3.7 exact subclaims, with actual-object identification.
3. **Revise tracker rows** to strike through newly confirmed completed *subclauses* of 3.7, 3.8, 4.2, 4.6–4.8, 5.1–5.3, 6.2, 6.6, 6.9–6.10, 6.13, 6.15 and 6.18. Their parent printed titles **must remain uncrossed** unless all clauses match.
4. **Prioritize the actual ζ(5) 4.4 quantitative family**: multiplier integrality/rapid decay, determinant energy, all-root spectral cap and effective thresholds. The archived `denominatorClearingNormalization_no_multiplierUpper` is a useful anti-circularity test.
5. Every later closure requires manuscript page + exact Lean declaration + pinned source SHA + CI/native compiler PASS + independent axiom audit + explicit distinction of conditional premises. Do not transform a proved corrected version into a claim about false original print.

**Proof count at this checkpoint:** seven exact complete printed items, zero entire-paper `!!!` formal closure, zero `!!!!` S-Tier admissions. The frozen `snditeration/main` Lean sources and earlier PASS-ONCE receipts are unchanged.
