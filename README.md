> **ALT construction — manuscript 6.1.**
> [Alternative target and prerequisites](Experimental/P06_01/Alt/Target.md) · [Proposed branch](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-01_prop_construction).
> Documentation only; no new Lean interface, axioms, build or proof tier. The inherited register below describes the main baseline.

# Zetahyperbolic — manuscript completion and Lean evidence

Formalization of *Spectral Theory and Diophantine Bounds for Hankel Determinants
of Odd Zeta Values* (Prince Anand, 21 October 2026; supplied 52-page manuscript),
using Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Workflow: `YOU_ARE_GOODWORKFLOWFRONTIER`; proof mode and execution target unchanged.

**Current boundary: 9 of 45 numbered proof statements have exact whole-statement
A-Tier evidence.** Proposition 3.2 has a complete **corrected** proof and is counted
separately. Other items contain useful verified components, source candidates,
open hypotheses, or printed claims requiring repair. These counts are an
inventory, not a percentage of mathematical work completed. No unconditional
ζ(5)/ζ(7) irrationality, RH, finite-witness closure, or full-paper completion is claimed.

## Experimental modularization

The [experiment index](docs/EXPERIMENTS.md) links **36 isolated branches** for the
unfinished original proof items, including the original formulation of corrected
3.2. Their typed prerequisite boundaries contain **51 named axioms** across the
branches; **7 branches add no new axiom**. All are **SOURCE_ONLY_UNCOMPILED**:
publication checks verified their bytes, but no Lean compilation, new target proof
or proof-tier promotion is claimed. The **9/45** exact-original count is unchanged.

Main contains only the index and [axiom policy](docs/EXPERIMENTAL_AXIOM_POLICY.md),
with no experimental Lean modules or changes to certified imports, build or CI.
Each unfinished row below links its branch; original statements, partial input
coverage and repairs remain explicit in its `Target.md`. Immutable commits, named
assumptions and source fingerprints are in [EXPERIMENTS.json](docs/EXPERIMENTS.json).

## Evidence snapshot

- Source reviewed: [`main@3b184ba109f065d973957a5735fb590fea4b0e35`](https://github.com/randogelist/snditeration/tree/3b184ba109f065d973957a5735fb590fea4b0e35), 26 October 2026.
- [Exact-source CI run 40288194429](https://github.com/randogelist/snditeration/actions/runs/40288194429), [job 121456771906](https://github.com/randogelist/snditeration/actions/runs/40288194429/job/121456771906): successful build, axiom audit and source-placeholder check. The full log reports **8,806 build jobs**, **1,317 theorem declarations checked by the allowlist**, and **312 printed axiom reports**. These are not manuscript-item counts. Inspected axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
- This README update is a source/evidence audit; it does not execute Lean or change the proof mode or execution target. Existing GitHub CI evidence remains separate from native Windows receipts.
- The published branch snapshot contains **`main` and 36 isolated experimental branches**; see the [experiment index](docs/EXPERIMENTS.md). These source-only branches add no certified paper proof. Merged branches, archive families and companion repositories remain separate provenance sources.
- The supplied PDF SHA-256 is `935767c0cda7468f376cd8eadc374077caf6c8a060351d3bea26ac3f838a9d0c`. Numbering was checked against the PDF and `provenance/original_manuscript_Zetahyperbolic.tex` in the supplied `ZETAHYPERBOLIC_10_STAGE_STITCH_v0_1_26_GOODWORKFLOWFRONTIER_TARGETED_COMMUTATIVITY_FIX.zip`.

The register below supersedes stale **status summaries**, not historical proof
receipts. In particular, the older ledger's missing 2.3 `RatFunc.eval` bridge,
unfinished corrected 3.2 pencil and 8/45 total are superseded by the current
source/audit evidence. `CHECKPOINT.json` is an earlier PR #14 receipt, not a
complete inventory of the current tree.

## Tier rules

| Mark | Meaning |
| --- | --- |
| `!` — B-Tier | A reasoned on-paper derivation, with explicit premises. A printed claim or source filename alone does not earn this mark. |
| `!!` — A-Tier | The exact declaration has compiled and its transitive axioms were audited. Its hypotheses and execution target remain attached to the claim. |
| `!!!` — conditional closure | A certified complete transfer chain to the target, with only the stated finite-witness admission outstanding. No item receives this mark here. |
| `!!!!` — accepted witness | An accepted concrete finite witness plus the certified downstream transfer. No item receives this mark here. |
| `OPEN; component !!` | Only the described component is A-Tier; the full printed item remains open. |
| `REPAIR; corrected/component !!` | A corrected result, counterexample or supporting component is verified; the literal printed statement is not certified. |
| `OPEN; source partial` | A partial result or candidate is located in the source register, but it has not been granted fresh destination certification by this audit. |

A theorem that is conditional **in the paper** can be a complete `!!` proof of
that exact conditional statement, as for Proposition 4.2. This does not prove
its hypotheses for a particular ζ-family and is not `!!!` finite-witness closure.
A successful build covers its import graph, not every `.lean` file in the tree.
Seventeen preserved candidate modules are outside the active root/audit import
graph; their existence is not a PASS.

## Chapter list

| Chapter | Contents | Numbered proof items | Whole printed items at `!!` |
| --- | --- | ---: | ---: |
| 1 | Introduction | 0 | — |
| [2](#chapter-2--algebraic-structure-and-canonical-basis-invariance) | Algebraic structure and canonical basis invariance | 4 | 4 |
| [3](#chapter-3--hyperbolicity-total-positivity-and-spectral-structure) | Hyperbolicity, total positivity and spectral structure | 9 | 1; corrected 3.2 separate |
| [4](#chapter-4--diophantine-approximation-heights-and-root-collapse) | Diophantine approximation, heights and ζ(5) root collapse | 8 | 2 |
| [5](#chapter-5--weight-seven-integrals-dual-pencils-and-double-poles) | Weight-seven integrals, dual pencils and double poles | 6 | 2 |
| [6](#chapter-6--structural-barriers-multiweight-couplings-and-further-results) | Structural barriers, multiweight couplings and further results | 18 | 0 |
| 7 | Discussion and open problems | 0 | — |
| **Total** | **35 theorems + 2 lemmas + 5 propositions + 3 corollaries** | **45** | **9** |

Definition 2.1, four remarks and Conjecture 4.11 are also indexed below, bringing
the full numbered inventory to 51. Page numbers refer to the supplied PDF.
Links to active proof modules inherit the immutable source/CI snapshot above;
links to gap documents locate candidates and blockers rather than certify them.

## Chapter 2 — Algebraic structure and canonical basis invariance

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Lemma **2.2** · p.4 | Pullback identity | **A-Tier `!!` — exact** | Full rational-domain scaled substitution and pullback identity, with k≥1. | [RationalPullbackAssembly](Zetahyperbolic/Section2/RationalPullbackAssembly.lean) |
| Lemma **2.3** · p.5 | Reflection and difference identities for $\tau_X^{(s)}$ | **A-Tier `!!` — exact** | Reflection and regular-domain finite difference identified with actual Mathlib RatFunc.eval iterated analytic derivative. Root includes RationalTaylor, superseding stale ledger API gap. Proof's Bernoulli parity errors repaired; regularity at zero explicit. | [RationalReflection](Zetahyperbolic/Section2/RationalReflection.lean); [RationalTaylor](Zetahyperbolic/Section2/RationalTaylor.lean) |
| Theorem **2.4** · p.6 | Canonical basis invariance | **A-Tier `!!` — exact** | Constructed primitive normalization and canonical basis invariance; actual determinant nonvanishing proved. | [BasisInvariance](Zetahyperbolic/Section2/BasisInvariance.lean); [PoleDiagonalization](Zetahyperbolic/Section2/PoleDiagonalization.lean) |
| Theorem **2.5** · p.6 | Lagrange pole diagonalization | **A-Tier `!!` — exact** | Actual Lagrange interpolation products, inverse Vandermonde, pole slope diagonalization and exact transformed pencil. | [PoleDiagonalization](Zetahyperbolic/Section2/PoleDiagonalization.lean); [LagrangeBasis](Zetahyperbolic/Section2/LagrangeBasis.lean) |

Additional numbered items (outside the 45-proof denominator):

- **Definition 2.1** (p.3) — Order-$s$ rational moment functional. Actual rational simple-pole domains and representation-independent order-s linear functional; definition itself is not a theorem.

## Chapter 3 — Hyperbolicity, total positivity and spectral structure

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **3.1** · p.7 | Universal hyperbolicity and zero-free disk | **A-Tier `!!` — exact** | Actual Gram positivity, exact degree, real roots avoiding zeta center, actual whitened spectrum, sharp 1/operator-norm radius and primitive-polynomial transport; structural admissibility only, no claim of pairwise-distinct roots. | [Unconditional](Zetahyperbolic/Section3/Unconditional.lean); [ActualSpectrum](Zetahyperbolic/Section3/ActualSpectrum.lean); [PrimitivePolynomial](Zetahyperbolic/Section3/PrimitivePolynomial.lean) |
| Proposition **3.2** · p.8 | Continuous hyperbolic pencil for all real $s > 1$ | **REPAIR; corrected `!!`** | Corrected real-s>1 positive Gram, nonsingular slope, exact degree, real roots and odd-s coincidence. Prefactor corrected to 2(2pi)^(s-1)/Gamma(s); literal paper prefactor is pi/2 times this. ContinuousParameter candidate not imported. | [ContinuousPencil](Zetahyperbolic/Section3/ContinuousPencil.lean); [ContinuousDensity](Zetahyperbolic/Section3/ContinuousDensity.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-02_construction) |
| Theorem **3.3** · p.8 | Total positivity, leading sign, and universal signature | OPEN; component `!!` | Exact weight-five leading sign and multiplicity-counted inertia/root-side counts. Part(1) full mixed-minor total positivity and Stieltjes determinacy remain open. Main's Carleman, shifted/mixed moment candidate sources are not imported; no A-tier inherited from source presence. Companion PR #46 verifies a generic factorial-growth Carleman criterion; actual moment bounds and uniqueness are still missing. | [PrincipalPencils](Zetahyperbolic/Section3/PrincipalPencils.lean); [PoleSigns](Zetahyperbolic/Section3/PoleSigns.lean); [SpectralInertia](Zetahyperbolic/Section3/SpectralInertia.lean); [companion criterion](#separate-companion-evidence); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-03_construction) |
| Theorem **3.4** · p.9 | Root interlacing and Dodgson condensation for principal minors | REPAIR; component `!!` | Principal-root reality, abstract signature restriction, and arbitrary-order polynomial block Dodgson identity proved. Actual constant first principal pencil refutes assuming r finite roots at each size. CauchyInterlacing, PrincipalRadius and actual PrincipalCondensation candidate not imported, so full interlacing/actual Dodgson endpoint remain open in active main graph. | [PrincipalPencils](Zetahyperbolic/Section3/PrincipalPencils.lean); [SignatureRestriction](Zetahyperbolic/Section3/SignatureRestriction.lean); [DodgsonCondensation](Zetahyperbolic/Section3/DodgsonCondensation.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-04_construction) |
| Corollary **3.5** · p.10 | Stieltjes J-fraction from interlacing roots | REPAIR; component `!!` | Actual admissible rank-one counterexample refutes literal continued fraction. General normalized Lanczos/no-breakdown and spectral-edge decay still open. | [ContinuedFractionCounterexample](Zetahyperbolic/Section3/ContinuedFractionCounterexample.lean); [ContinuedFractionObstruction](Zetahyperbolic/Section3/ContinuedFractionObstruction.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-05_construction) |
| Corollary **3.6** · p.11 | Stieltjes reciprocal-root power sums | REPAIR; component `!!` | Corrected even-moment estimator bounds and convergence at actual spectral center. All-order strict finite-atom Hankel positivity refuted; odd-m sign needs repair. Arbitrary rational-shift/log-derivative and full finite-rank corrected clauses not supplied by local estimator endpoints alone. | [ReciprocalMoments](Zetahyperbolic/Section3/ReciprocalMoments.lean); [ReciprocalMomentLimit](Zetahyperbolic/Section3/ReciprocalMomentLimit.lean); [ContinuedFractionObstruction](Zetahyperbolic/Section3/ContinuedFractionObstruction.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-06_construction) |
| Theorem **3.7** · p.11 | Turán non-negativity and Newton log-concavity | OPEN; component `!!` | All-order actual derivative Turan weak/strict/equality, sharp center ratio, normalized coefficient Newton strict/equality criteria, and strict centered Newton hierarchy proved. Individual nonvanishing of every intermediate centered coefficient remains unproved; generic-distinctness argument invalid. | [NewtonTuran](Zetahyperbolic/Section3/NewtonTuran.lean); [ActualNewtonTuran](Zetahyperbolic/Section3/ActualNewtonTuran.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-07_construction) |
| Theorem **3.8** · p.12 | Christoffel–Darboux pole representation and Jacobi derivative identity | OPEN | ChristoffelDarboux and LaplaceJacobiIdentity candidates exist but are not imported or covered by current main audit. Do not promote source declarations or historical finite-operator components to full actual CD/Laplace identity. | [ChristoffelDarboux](Zetahyperbolic/Section3/ChristoffelDarboux.lean); [LaplaceJacobiIdentity](Zetahyperbolic/Section3/LaplaceJacobiIdentity.lean); [CONTINUATION_MAIN_MERGE_RESOLUTION_20261026](docs/CONTINUATION_MAIN_MERGE_RESOLUTION_20261026.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-08_construction) |
| Theorem **3.9** · p.13 | Hyperbolicity for Hurwitz and Dirichlet Hankel determinants | OPEN | Actual Hurwitz/Dirichlet positive measures and pole-moment identifications absent from active graph. Historical companion finite character/Fekete components do not close full statement. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-09_construction) |

Additional numbered items (outside the 45-proof denominator):

- **Remark 3.10** (p.14) — Non-classicality of the Hankel family. Remark: non-classicality needs precise invariant/exclusion proof; printed Favard root-birth argument is not a standalone obstruction.

## Chapter 4 — Diophantine approximation, heights and root collapse

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **4.1** · p.14 | Spectral irrationality measure criterion | OPEN; component `!!` | Local complex-root comparison, lattice index and rational transfer; effective threshold requires explicit computable onset/rates. Printed existence of effective b₀ from bare eventual bounds is not certified. | [TransferComplete](Zetahyperbolic/Section4/TransferComplete.lean); [EffectiveBudget](Zetahyperbolic/Section4/EffectiveBudget.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-01_construction) |
| Proposition **4.2** · p.15 | Transfer criterion for algebraic approximations of degree $d \ge 1$ | **A-Tier `!!` — exact**; printed hypotheses retained | Exact lattice, degree, nonzero quadratic decay, complex-root separation and height-limsup assumptions imply the printed bound for all algebraic α with bounded extension degree and large naive height. Actual ζ5 input estimates are separate. No effective B₀ is claimed in the printed proposition. | [AlgebraicHeight](Zetahyperbolic/Section4/AlgebraicHeight.lean) |
| Proposition **4.3** · p.15 | Ultrametric zero-free disk over $\mathbb{Q}_p$ | **A-Tier `!!` — exact** | Exact norm-preserving zero-free disk over ℂ_p for integer Q with Q(ξ)≠0; actual primitive polynomial specialization included. Specific ζ-family center valuation is separate. | [ActualPrimitivePadicDisk](Zetahyperbolic/Section4/ActualPrimitivePadicDisk.lean) |
| Theorem **4.4** · p.16 | Sharpened spectral bound and effective irrationality measure for $\zeta(5)$ | OPEN; component `!!` | Actual primitive polynomial with positive normalization, exact degree, nonzero center and finite identities; explicit multiplier, uniform quadratic decay, spectral cap and exponent 25687 remain open. The supplied PDF states the spectral cap 11.411 and measure exponent 25687. | [PrimitivePolynomial](Zetahyperbolic/Section3/PrimitivePolynomial.lean); [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-04_construction) |
| Theorem **4.5** · p.18 | Irrationality and effective measure for $b\zeta(5) + a\zeta(3)$ | OPEN; source partial | Finite weight-shift determinant reweighting only; coupled density/Loewner bounds, p-adic cancellation, decay and effective measure open. | [ROUND_AUDIT_2026-10-26_ADDITIONAL_CROSSINGS](docs/ROUND_AUDIT_2026-10-26_ADDITIONAL_CROSSINGS.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-05_construction) |
| Theorem **4.6** · p.19 | Two-sided determinant bounds and coefficient heights | REPAIR; component `!!` | Finite leading-value/Gram/log conservation only; quadratic asymptotics and heights open. Printed use of upper multiplier-rate bound as a lower bound needs repair. | [PotentialGap](Zetahyperbolic/Section6/PotentialGap.lean); [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-06_construction) |
| Theorem **4.7** · p.21 | Macroscopic exponential root collapse and root separation | OPEN; source partial | Finite cap+average cluster count and root-distance transport; actual family uniform cap/average and arithmetic separation open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-07_construction) |
| Proposition **4.8** · p.21 | Rational root exclusion and degree bounds for cluster factors | REPAIR / OPEN; source partial | Factor/root-distance inequalities only; rational-root exclusion and effective degree bounds open. Printed proof reverses lower gap into upper cluster bound. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-08_construction) |

Additional numbered items (outside the 45-proof denominator):

- **Remark 4.9** (p.22) — Spectral bounds and variational conjecture for $\rho_5^*$. Variational envelopes, sandwich constants and claimed consequences not certified as a whole.
- **Remark 4.10** (p.22) — Lee–Yang phase transition at $\zeta(5)$. Free-energy limit and first-order singularity remain unproved; zero pinching alone does not establish a phase transition.
- **Conjecture 4.11** (p.22) — Variational spectral-rate limit. Existence of normalized spectral-norm limit and equality with variational value unproved.

## Chapter 5 — Weight-seven integrals, dual pencils and double poles

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **5.1** · p.22 | Two-variable Beukers measure for $\zeta(7)$ | **A-Tier `!!` — exact** | Actual positive measurable unit-square density, all diagonal/offdiagonal moment identities and explicit rational offdiagonal witness. | [BeukersOffDiagonal](Zetahyperbolic/Section5/BeukersOffDiagonal.lean); [BeukersDensity](Zetahyperbolic/Section5/BeukersDensity.lean); [BeukersRationalMoments](Zetahyperbolic/Section5/BeukersRationalMoments.lean) |
| Theorem **5.2** · p.23 | Dual hyperbolicity and Krein-space decomposition of the two-variable $\zeta(7)$ pencil | REPAIR; component `!!` | Local finite dual spectrum under real row separation and actual monomial/coefficient Krein identities; full arbitrary-L² extension and all-dimensional cones remain open. Fixed-K positive/negative cones need dimension repair. | [ActualDualSpectrum](Zetahyperbolic/Section5/ActualDualSpectrum.lean); [KreinMonomial](Zetahyperbolic/Section5/KreinMonomial.lean); [KreinPolynomial](Zetahyperbolic/Section5/KreinPolynomial.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-02_construction) |
| Proposition **5.3** · p.24 | Two-variable Beukers measure and dual pencil for $\beta(4) = L(4, \chi_{-4})$ | OPEN; source partial | Low-node β4 tensor/Gram calculations only; actual two-variable integral, moments and dual pencil open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-03_construction) |
| Theorem **5.4** · p.25 | Cancellation of higher zeta values on even pole pairs | **A-Tier `!!` — exact** | Actual τ on simple even-pole pairs, every j≥1 including j=1, and finite rational linearity. | [EvenPoleCancellation](Zetahyperbolic/Section5/EvenPoleCancellation.lean) |
| Theorem **5.6** · p.26 | Weight-seven prime-sum evaluation and pole-ordered refinement | OPEN; source partial | Rational constant signs do not establish floor-function partition, prime-sum integrals or q-adic gain. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-06_construction) |
| Theorem **5.7** · p.28 | Simultaneous double-pole Hankel determinant for $\{1, \zeta(5), \zeta(6)\}$ | OPEN | Actual double-pole decomposition, local determinants/valuations and lower-minor bounds unproved. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-07_construction) |

Additional numbered items (outside the 45-proof denominator):

- **Remark 5.5** (p.25) — Simple-pole scope restriction. 5.4 covers simple poles only; no higher-order extension is asserted or required here.

## Chapter 6 — Structural barriers, multiweight couplings and further results

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **6.1** · p.29 | Divided-difference $p$-adic valuation law and intrinsic $p^{-6}$ barrier | OPEN | Actual divided-difference valuation, Mellin bridge and intrinsic p⁻⁶ obstruction unproved. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-01_construction) |
| Theorem **6.2** · p.31 | Simultaneous weight-$(6, 7)$ Beukers functional with zero denominator overhead | OPEN; source partial | Exact divided differences and 6d_K⁷ denominator; simultaneous ζ6/ζ7 analytic functional and claimed zero overhead remain open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-02_construction) |
| Theorem **6.3** · p.32 | Unconditional $q$-adic non-vanishing and explicit positive-cone approximations for $G_{\mathcal{A}}^{(7)}(X)$ | REPAIR / OPEN | Part (2) has an external rational h=4 negative-direction counterexample, not a Lean replay; independent q-adic part (1) remains open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-03_construction) |
| Theorem **6.4** · p.33 | Character–Vandermonde sign cancellation and unconditional hyperbolicity for $\beta(4)$ | OPEN; source partial | Finite character-Vandermonde cancellation and two/three-node Gram models; actual β4 analytic pencil and global arithmetic open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-04_construction) |
| Theorem **6.5** · p.34 | Unconditional $q$-adic non-vanishing for $\Delta_K^{(\beta(4))}(0)$ | OPEN | Specified q≡1 mod8 determinant valuation and local unit-block proof missing. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-05_construction) |
| Theorem **6.6** · p.35 | Generalized multi-weight positive-definite pencil | OPEN; source partial | Finite anchored positive cone, full-degree real spectrum and Turán under matrix assumptions; actual multiweight density/arithmetic inputs open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-06_construction) |
| Theorem **6.7** · p.37 | Universal multi-weight two-variable Beukers Krein decomposition | OPEN | Universal actual two-variable multiweight measure, infinite Krein decomposition/cones and q-adic input missing. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-07_construction) |
| Corollary **6.8** · p.38 | Unconditional three-term linear independence cone for $\{1, \zeta(3), \zeta(5)\}$ | OPEN | Three-term linear independence and effective forms inherit unproved 4.5 arithmetic/decay hypotheses. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-08_construction) |
| Theorem **6.9** · p.38 | Triple-pole and multi-weight Hankel determinants | OPEN; historical companion component `!!` | Historical companion Hermite determinant-unit lemma under prime, distinct-node and congruence hypotheses. Actual triple-pole rows, their congruence and the printed valuations remain open; not integrated here. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [verified donor receipt](#separate-companion-evidence); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-09_construction) |
| Theorem **6.10** · p.39 | Universal potential-gap identity and vanishing of quadratic derivative growth in two variables | REPAIR; component `!!` | Local actual finite potential conservation and corrected rate-direction counterexample. Imported CoefficientGramGrowth proves normalized log det(CCᵀ)→0 under row rank and polynomial entry bounds, using a weaker finite bound than printed Hadamard. Full limiting potential gap and strict reweighting remain open. | [PotentialGap](Zetahyperbolic/Section6/PotentialGap.lean); [CoefficientGramGrowth](Zetahyperbolic/Section6/CoefficientGramGrowth.lean); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-10_construction) |
| Theorem **6.11** · p.40 | The $p^{-(2k-1)}$ distribution growth law and 2-adic polynomial-quotient obstruction for $\beta(2k)$ | OPEN; source partial | Odd-square scaling/parity only; Euler distribution and odd/2-adic valuation laws open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-11_construction) |
| Theorem **6.12** · p.42 | Full-dimension sign-flip restoration of positive definiteness and $q$-adic non-vanishing for pure $\beta(4)$ | OPEN | Actual sign-flipped full-dimensional positivity, rational cutoff with spectral margin and q-adic nonvanishing missing. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-12_construction) |
| Theorem **6.13** · p.43 | Central-factorial secant differential identity, Laplace mode annihilation, and unilateral $(h,0)$ root signature for all $k\ge 1$ | REPAIR / OPEN; source partial | Finite central-factorial/secant identity and positive envelope; printed series sign needs correction, differentiated infinite sum and β-pencils remain open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-13_construction) |
| Theorem **6.14** · p.45 | Even-pole scaling via $\cosh(2\pi v)$ and coupled positive-definite pencils for $b\zeta(5)+a\beta(4)$ and $b\zeta(5)-a\beta(2)$ | OPEN | Even-pole cosh scaling, aligned moments and uniform coupled spectral/arithmetic bounds missing. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-14_construction) |
| Theorem **6.15** · p.46 | Arithmetic transcendence, strictly positive one-variable measure, and rank-one Padé pencil for $\beta(2k+1)$ across all $k\ge 0$ | REPAIR / OPEN; source partial | Odd β rational π-powers, qualitative transcendence/finite independence and k=0 moments; effective measures, all-k rank-one law and printed exterior asymptotic not certified. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-15_construction) |
| Theorem **6.16** · p.47 | Generalized multi-weight Zeta–Beta positive-definite pencil | OPEN; historical companion component `!!` | Historical companion compact positive-ratio comparison with explicit endpoint positivity and ratio identity. Actual mixed ζ–β weight, endpoint behavior, spectral and arithmetic conclusions remain open; not integrated here. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [verified donor receipt](#separate-companion-evidence); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-16_construction) |
| Theorem **6.17** · p.48 | Universal two-variable Beukers Zeta–Beta pencil, Krein decomposition, and $q$-adic non-vanishing | OPEN; historical companion component `!!` | Historical companion corrected harmonic windows, support disjointness and index nondivisibility. Actual combined measure, infinite Krein decomposition and highest-weight determinant nonvanishing remain open; not integrated here. | [PAPER_GAP_TRACKER](docs/PAPER_GAP_TRACKER.md); [verified donor receipt](#separate-companion-evidence); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-17_construction) |
| Theorem **6.18** · p.49 | Principal-minor 2-adic integrality law, dyadic height bounds for Zeta–Beta pencils, and multi-weight effective measures | OPEN; source partial | Dyadic numerator/denominator degree and quotient-vanishing threshold only; integrality, multiplier, height loss and effective measure open. | [PAPER_GAP_TRACKER](docs/PAPER_GAP_TRACKER.md); [experiment](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-18_construction) |

## Separate companion evidence

The companion repository is a source of reusable components, not an automatically
accepted extension of this repository. Its current `main` at
[`211b362c16ff6ef73e9a5f2f70c5cbb9a444cf80`](https://github.com/randogelist/zetahyperbolic-axiom/tree/211b362c16ff6ef73e9a5f2f70c5cbb9a444cf80)
has [failed CI 40281177876](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40281177876).
The following earlier exact-source receipts were inspected independently; none
closes the corresponding whole paper item or certifies a new destination import.

| Item | Verified component | Exact source and successful run | Open boundary |
| --- | --- | --- | --- |
| 3.3 | `LeanPaper.CarlemanFactorialCriterion.carleman_not_summable_of_factorial_growth` | Unmerged [PR #46](https://github.com/randogelist/zetahyperbolic-axiom/pull/46), source `82fcf7b31da336585fe81bd5b75f0043a69fec4e`; [CI 40279223299](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40279223299) | Generic positive moment sequence with a supplied factorial upper bound; actual manuscript bound and Stieltjes uniqueness remain open. |
| 6.9 | `Zeta5.HermiteBasisCore.det_coeffMatrix_unimodular'` | Source `ef6cc78ea8ba36f71f38718a3b6af07d4d69217c`; [CI 40270088000](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40270088000) | Prime, distinct-node and congruence inputs; actual triple-pole table/congruence and valuation transfer remain open. |
| 6.16 | `Zeta5Merge.Theorem6_16.weight_comparison_of_compact_ratio` | Source `9814065ae1cba0098f873fea4fc0782dcba23187`; [CI 40262637451](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40262637451) | Positive endpoints and an explicit ratio identity; actual mixed-weight and arithmetic identification remain open. |
| 6.17 | Corrected `harmonic_windows`, `high_unique_multiple`, support and divisibility lemmas | Source `8da5614e6b8994fd163db024c51e3f3512cd1d7f`; [CI 40260089735](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40260089735) | Finite combinatorics only; not the original beta-pencil determinant valuation. |

All four cited companion logs contain an independent visited-set all-project
axiom audit with `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` and only
`Quot.sound`, `Classical.choice`, `propext`. Historical success remains attached
to its source and dependencies; it does not turn the failed current main into PASS.

## Source reconciliation and continued checks

The initial review covered the 25 supplied ZIPs, the manuscript and the historical
workflow TXT, together with the current repository, merged PR lineage and the
registered companion. The `v1_0_15` workflow attachment is historical; the user's
`v1_0_25` workflow remains authoritative. No independent mode/target lock is changed
by maintaining this register.

Useful source families remain distinct:

- The assembled general chain and anchor-chain v0.2.6 preserve actual analytic/spectral construction and conditional normalized-decay transfers. The newer destination source/CI, rather than a ZIP label, governs this README's integrated status.
- Paper45, Paper10 and ten-stage-stitch packages contain overlapping finite algebra, moment and Gram work with different compiler frontiers. Their module counts and receipts must not be added together.
- ζ3 Euler/elementary/Mahler, IMPACTG, GP7/Chebyshev, odd-zeta 3×3 and finite-witness packets supply possible components. Ordinary convergence, finite checker examples or a finite score do not establish all-denominator decay or irrationality.
- See [archive frontier](docs/ARCHIVE_FRONTIER.md), [cross-project intake](docs/CROSS_PROJECT_SOURCE_INTAKE_20261026.md), [cross-branch audit](docs/CROSS_BRANCH_RESOLUTION_AUDIT_2026-10-25.md), [gap register](docs/PAPER_GAP_REGISTER.md) and [closure queue](docs/NONINTERFERING_BRANCH_CLOSURE_QUEUE.md) for source locations and unresolved transfers.

For each subsequent check:

1. Refresh all live branches, merged/open PRs, registered source repositories and relevant archive revisions. Record immutable source SHAs; do not treat branch names as fixed evidence.
2. Compare the exact printed definition, quantifiers and hypotheses with each candidate declaration, including actual ζ/moment identification and uniformity in all orders.
3. Verify membership in the built/audited import graph, source/dependency/toolchain fingerprints, the successful run on that source, and actual axiom logs. Keep Windows and GitHub CI evidence separate; reuse only compatible, unchanged passed artifacts.
4. Update the affected README rows, source links and whole-item counts. Preserve partial and corrected results explicitly. Never promote a stale receipt, filename, printed proof, unchecked source, external numeric countercheck, or assumed conclusion.
5. Keep the original statement and any correction separately identified. Do not count a corrected theorem as closure of its original false formulation. No proof-source edits, merges or new compilation are implied by a documentation check.

The next recorded mathematical endpoint is [Theorem 5.2(2), the actual arbitrary-L²
Beukers–Krein extension](docs/NEXT_ENDPOINT.md); its monomial and finite coefficient
pieces are already frozen. Full manuscript work also needs the independent open
rows above, especially quantitative decay/arithmetic inputs and repaired statements.

## Existing build and audit entry points

The project uses Lean 4.33.0 with the Mathlib revision pinned above. In the
repository's provisioned CI environment:

```sh
lake build Zetahyperbolic
lake env lean Zetahyperbolic/Audit.lean
```

The [CI workflow](.github/workflows/lean.yml), root
[`Zetahyperbolic.lean`](Zetahyperbolic.lean) and
[`Audit.lean`](Zetahyperbolic/Audit.lean) identify the active import/audit graph.
No build was executed to produce this documentation update. Native Windows
cache/runner receipts remain a separate execution target; no Linux artifact is
silently reused as Windows verification.

Earlier receipts remain under [docs/receipts](docs/receipts/), with exact
[manuscript repair notes](docs/MANUSCRIPT_REPAIRS.md) and
[Section 3 corrections](docs/SECTION3_CORRECTIONS.md). Historical source packets
and proof files are unchanged by this register.
