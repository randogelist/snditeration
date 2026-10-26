# Repeat-round proof audit — 26 October 2026

## 1. Established proof-tier definitions

Source: supplied `YOU_ARE_GOODWORKFLOWFRONTIER_WORKFLOW_DEFINITION_v1_0_15.txt`; these are the **certification** levels, not subjective priorities.

| Marker | Proof tier | Gate |
|---|---|---|
| `!` | **B-Tier** | On-paper mathematical derivation, conditional on reasoning, not yet Lean verified |
| `!!` | **A-Tier** | Exact Lean theorem parsed/elaborated/compiled and transitively axiom-audited, with no `sorryAx`, hidden axioms or unstated hypotheses |
| `!!!` | **Formal closure** | An A-Tier *conditional* chain reduces the target to acceptance by a finite terminating witness checker; accepted concrete witness absent |
| `!!!!` | **S-Tier** | Concrete finite raw-data witness actually passes a terminating checker, and the downstream Lean proof is compiled and axiom-audited |

A theorem may be A-Tier **only as an implication with explicit assumptions**. A corrected statement or complete subclause is not proof of a false/larger original theorem. The finite-witness gates only apply when the final target is formulated as a finite-witness problem; ordinary Lean paper theorems can be A-Tier without a witness architecture.

## 2. Manuscript items already crossed off in the combined audited repositories

The original 52-page PDF dated 21 October 2026 has SHA-256 `935767c0cda7468f376cd8eadc374077caf6c8a060351d3bea26ac3f838a9d0c`, verified against the supplied PDF again on 26 October.

| Exact printed item | Whole-item gate | Source provenance |
|---|---|---|
| ~~2.2~~ Rational pullback | `!!` A-Tier, **snditeration local** | `Section2/RationalPullbackAssembly.lean` at pinned main and companion duplicate |
| ~~2.3~~ Tau reflection/difference | `!!` A-Tier, **companion** | `LeanPaper.Section2RatFuncTranslation`, `Section2DifferenceDerivative.tau_difference_span_derivative`; all-regular-RatFunc coefficient identity remains a *stronger local extension*, not part of the printed obligation |
| ~~2.4~~ Canonical basis invariance | `!!` A-Tier, **snditeration local** | `Section2/BasisInvariance.lean` |
| ~~2.5~~ Lagrange pole diagonalization | `!!` A-Tier, **snditeration local** | `Section2/PoleDiagonalization.lean`, `LagrangeBasis.lean` |
| ~~3.1~~ Universal actual odd-weight hyperbolicity/sharp finite disk | `!!` A-Tier, **snditeration local** | `Section3/Unconditional.lean`, `ActualSpectrum.lean` |
| ~~4.3~~ Norm-preserving complex p-adic disk | `!!` A-Tier, **companion** | `LeanPaper/ImportedSection4/Proposition_4_3_ComplexPadicDisk.lean` |
| ~~5.4~~ Even-pole cancellation, including j=1 | `!!` A-Tier, **companion** | `LeanPaper/Section2TauLinear.lean` |

**7 of 45 exact whole printed items**, 4 in [snditeration/main@c521749](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420), 3 additionally in [zetahyperbolic-axiom/main@86ca99a](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968). GitHub Actions [local PASS 40186793090](https://github.com/randogelist/snditeration/actions/runs/40186793090) and [companion PASS 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). The companion's `validation/linux/acceptance.json` reports 219 compiled modules/2,489 audited theorem declarations; these are **not** counts of complete manuscript theorems.

## 3. Round A — all current GitHub branches, PRs, and build gates

The 17 `snditeration` branches and five `zetahyperbolic-axiom` branches were re-enumerated on 26 October. **Both verified `main` heads are unchanged since the 25 October audit.** The only outstanding wide `snditeration` continuation, [PR #15](https://github.com/randogelist/snditeration/pull/15), head `0cee4ea2`, remains [CI FAILED, run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699), with source errors in continuous-weight, interlacing, Jacobi/Laplace, two-variable Beukers and coefficient-growth modules. No additional full theorem is promoted from this PR.

The companion's 219-module [proof-integrity JSON](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/validation/linux/proof_integrity.json) reports standard axioms `propext`, `Classical.choice`, `Quot.sound`, no custom axioms, and no proof placeholders. The source-level semantic status report still distinguishes **7 complete / 21 partial / 10 absent / 7 blocked** printed items.

## 4. Round B — detailed actual theorem types (new, narrowly crossed subclaims)

The following declarations were directly inspected in the *pinned passing companion source*. The text before each semicolon is a **completed subclaim**, not an assertion that its parent manuscript theorem is fully proved.

| Parent manuscript item | Newly sharpened crossing | What remains open |
|---|---|---|
| **3.4(1)** | ✓ ~~Exact degree of every actual principal determinant equals the rank of its slope; number of real roots counted with multiplicity equals that rank~~: `LeanPaper.PrincipalMinorRank.original_principal_degree_eq_rank`, `original_principal_real_roots_card_eq_rank`, `original_leading_degree_and_root_count` | Rank-aware *interlacing* between compatible principal spectra and correction of printed “r roots” when slope singular |
| **3.5** | ✓ ~~Correct normalized two-level and three-level finite Schur/continuant determinant identities~~: `LeanPaper.Section3ContinuedFractions.corollary_3_5_two_level_schur_identity`, `normalized_three_schur_identity`, `normalized_three_continuant_eq_det` | Full actual cyclic Lanczos/J-fraction for all orders, determinant-ratio prefactors, and the false printed formula |
| **3.7(1)** | ✓ ~~Actual all-derivative Turán nonnegativity/strictness and multiple-zero equality criterion~~: `LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan`, `..._strict`, `..._equality` | Parent theorem still claims unsupported nonvanishing of every intermediate *centered coefficient* |
| **3.7(2)** | ✓ ~~Actual coefficient Newton weak inequality and exact strict-vs-nonstrict criterion~~: `LeanPaper.NormalizedNewton.actual_primitive_coefficient_newton`, `LeanPaper.ActualStrictNewton.actual_coefficient_strict_criterion` | Does not imply all coefficients are nonzero |
| **3.7(3)** | ✓ ~~Strict centered normalized Newton inequality for all eligible orders of the actual family~~: `LeanPaper.ActualStrictNewton.actual_centered_newton_strict` | “Generic distinctness ⇒ all intermediate coefficients nonzero” in the printed reasoning is invalid |
| **4.2** | ✓ ~~Conditional degree-d algebraic-root lower bound with actual upper limsup height~~: `LeanPaper.Section4AlgebraicLimsup.algebraic_transfer_limsup`, plus constructed `Section4Resultant`/conjugate bounds | An exact Lean wrapper from algebraic numbers and minimal polynomials, actual arithmetic estimates and any genuine effective-onset claim |
| **4.7** | ✓ ~~General finite cap + average ⇒ cluster percentage and conditional 1.40% rational arithmetic~~: `PaperOrder.Section4.theorem_4_7_cluster_fraction_lower_bound`, `...cluster_percentage_arithmetic` | Actual K-dependent spectral cap, determinant average, separation and effective rate |
| **6.17 proof steps** | ✓ ~~Claims that all lower harmonic denominators are q-integral and the leading scalar block is universally a q-unit~~ are **refuted** by exact Lean countercalculations: `LeanPaper.BetaHarmonicIndexObstruction.lower_sum_not_eleven_integral` and `forty_one_diagonal_pole_drop` | Correct odd-index/pole ranges and the full conditional q-adic theorem. **A-Tier is attached to counterexamples, not to the printed theorem** |

Previously established completed subclauses remain crossed in [the 25 October repeated audit](MULTI_ROUND_CROSS_AUDIT_2026-10-25.md), including all-order Dodgson, corrected reciprocal-moment rank/distance bounds, finite relative/pole characteristic polynomial/trace, coefficient-gram positivity, conditional arithmetic index selection, finite triple-pole Hermite congruence, the finite 6.10 determinant identity, and qualitative odd-beta transcendence.

## 5. Round C — original PDF: two independent arithmetic-proof direction errors

**This round checked the actual supplied PDF**, not only prior source summaries.

- **Theorem 4.6(2), PDF pp. 16, 20–21 (NEW TRACKER EXPLICIT WARNING).** The manuscript assumes `A_M ≤ −2.32425`, and proves a separate normalized factor rate `2.557199...`. It then writes `A_M+2.557199 ≥ −2.32425+2.55690 >0.23`. The displayed lower bound **does not follow** from the stated *upper* bound on `A_M`. For example, `A_M = −3` satisfies the original upper bound but makes the sum negative. To prove the leading-coefficient rate `>0.23`, one needs a **lower bound** such as `A_M > −2.327199...` (or the stronger `A_M ≥ −2.32425`) plus justified rounding. The inequality may be true, but the paper's cited premise does not prove it. Add a separate effective lower-rate input rather than swapping `≤` to `≥` without justification.
- **Proposition 4.8(1), PDF pp. 21–22.** The paper obtains `|r−ζ(5)| ≥ exp(−11.411K)` from the operator-norm cap, then treats it as though *every* root satisfied the opposite *upper* bound `≤ exp(−11.411K)`. Thus the step choosing `τ=11.411` to exclude rational roots is unjustified. The finite factor-distance inequalities in **4.8(2)** are separately valid/audited and remain crossed. A new root-clustering or arithmetic exclusion argument is required for 4.8(1).
- **Proposition 3.2 / Corollaries 3.5–3.6 / Theorem 3.7(3) / Theorems 6.13, 6.15:** established normalization, continued fraction, finite-atomic rank, coefficient nonvanishing, product sign and exterior Szegő-asymptotic repairs still stand.
- **Theorem 6.3(2)**: an independent exact-rational h=4 certificate in [the companion's counterexample review](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/docs/BEUKERS_POSITIVITY_COUNTEREXAMPLE.md) refutes the printed positive cone with a negative quadratic direction, under a rigorous ζ(7) interval. That certificate is **not yet replayed inside Lean**, so report it as independently checked arithmetic + analytic evidence, not kernel A-Tier of a counterexample.

## 6. Round D — archived Lean ZIPs and conditional/witness admission audit

- `zeta5-spectral-lean (1).zip`: the checked `ManuscriptChain.MAIN_CHAIN_IRRATIONAL_REDUCED` implication explicitly takes `MainNormalization`, `BaseValuePositive`, `MultiplierUpper`, `ArchimedeanUpper`; the quantitative 25687 theorem additionally requires spectral and index-budget data. The package even proves `denominatorClearingNormalization_no_multiplierUpper`: ordinary denominator clearing **cannot** satisfy the required negative quadratic multiplier bound.
- `Zetahyperbolic-general-assembled-lean433 (2)/(3).zip`: source and receipts for unconditional general odd-weight **spectral** theorem, but all-odd/ζ5 **irrationality** is conditional on unproved concrete decay estimates; a theorem named `ZETA5_DIRECT_IRRATIONALITY` is not an unconditional proof by itself.
- `ZETA5_NATIVE_WITNESS_SEARCH_v0_1_0 (2).zip`: finite numerical polynomial checks include small explicit bounds, but the source README explicitly states `GLOBAL_IRRATIONALITY=NOT_CLAIMED`; no all-denominator or finite-witness RH admission is demonstrated.
- `ZETAHYPERBOLIC_PAPER45_TEN_STAGE_LEAN_v0_1_20_FINITE_GRAM_AUDIT.zip` and ten-stage archive relatives: finite spectral/Gram modules and workflow checkpoints, **not** the missing rate/prime/potential bounds for the 45-item manuscript.

No historical ZIP supplies a newly **certified exact complete printed** result beyond the seven current GitHub A-Tier closings. Formerly passed Windows native checkpoints remain as separately qualified receipts, not substitutes for current GitHub CI/dependency fingerprints.

## 7. Updated verdict and workflow

- **Exact completed original printed items: 7/45**, of which four are certified in `snditeration/main` and three only in the companion pinned repo. **Unchanged after four new audit rounds.**
- **Newly sharpened crossings:** 3.4(1) rank-sensitive degree and multiplicity count; 3.5 finite normalized 2-/3-level Schur/continuant identities; exact 3.7(1–3) subtheorems; generic degree-d conditional algebraic transfer and 4.7 finite cluster rate; explicit 6.17 local proof-step refutations.
- **New mathematical gap flag:** Theorem 4.6(2)'s use of an upper multiplier-rate bound as a lower bound, independent of the known 4.8(1) reversed root-distance direction.
- **Open critical chain:** the actual `K=30n` family arithmetic multiplier/integrality, nonzero determinant decay, uniform spectral bound `‖B_K‖₂≤exp(11.411K)`, and effective index/onset sufficient to deduce the printed ζ5 exponent **25687**. The K=40n external Fauzan code cannot be silently substituted.
- **No** whole-paper `!!!` formal closure, `!!!!` S-Tier admitted witness, unconditional ζ5 or ζ7 irrationality from this paper, or RH certificate was found.

**Update protocol:** retain this snapshot and the unchanged compiled sources; upgrade local item statuses only after an exact theorem import, full CI/build, and complete transitive axiom audit, with fully elaborated hypotheses visible. The tracker is documentation-only.
