# Persistent paper-gap ledger — snditeration

**Purpose:** maintain an exact, actionable inventory of the parts of the 52-page, 21 October 2026 Zetahyperbolic manuscript that are **not yet proved in the active `snditeration` Lean project**. This branch is an enduring tracking surface, not an assertion of manuscript closure.

**Frozen comparison snapshot (2026-10-25):**
- `snditeration/main` commit [`c521749`](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420); [local ledger](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/docs/FORMALIZATION_LEDGER.md), [CHECKPOINT](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/CHECKPOINT.json), [CI pass](https://github.com/randogelist/snditeration/actions/runs/40186793090). The existing receipt records 846 theorem declarations checked under standard Lean axioms, not 846 complete manuscript theorems.
- `zetahyperbolic-axiom/main` commit [`86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968); [45-item ledger](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/docs/FORMALIZATION_STATUS.md) and [successful Actions run](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). That different codebase reports 219 locally compiled and audited modules; 7 exact printed items complete, 21 partial, 10 absent, 7 blocked. **These are external comparison statuses, not automatic `snditeration` proofs.**
- `snditeration/feat/zetahyperbolic-continuation-20261025` adds 50 changed files spanning Sections 2–6 but its latest CI [failed](https://github.com/randogelist/snditeration/actions/runs/40188938699); use as **unverified candidate source**, not a new PASS.

## Status semantics

`PASS` = exact audited `snditeration/main` statement(s) reported in its ledger; `PARTIAL` = substantial audited local components but printed item incomplete; `CONDITIONAL TRANSFER` = rigorous theorem requiring explicit family-dependent premises; `REPAIR` = printed formula/claim cannot be admitted literally; `CORRECTED ONLY` = a mathematically corrected theorem, not the original print; `OPEN` or `NOT IN MAIN` = no complete local printed theorem certified. The external column refers **only** to the pinned cross-repository review. An archive ZIP, filename, or locally failed candidate never upgrades proof status.

## Manuscript-by-manuscript gap register

| # | PDF item | Name | `snditeration/main` | Other Leaned Paper | Actual open bridge for `snditeration` |
|---:|:---|:---|:---|:---|:---|
| 1 | 2.2 | Rational functional pullback | PASS | Verified | None on `snditeration/main`: full actual rational-function pullback. Freeze the audited theorem. |
| 2 | 2.3 | Reflection and difference identities for Tau | PARTIAL | Verified | Close analytic derivative-at-zero identity for the canonical partial-fraction coefficient on the actual regular RatFunc domain. The algebraic identity and regularity are done. |
| 3 | 2.4 | Canonical basis invariance | PASS | Verified | None for audited basis transport and primitive normalization in current source. |
| 4 | 2.5 | Lagrange pole diagonalization | PASS | Verified | None for audited actual Lagrange interpolation, pole slopes and Vandermonde factorization. |
| 5 | 3.1 | Universal hyperbolicity and zero-free disk | PASS | Verified | None for actual odd-weight Gram/spectrum, primitive degree and the sharp operator-norm zero-free disk. This is not yet a quantitative exponential bound. |
| 6 | 3.2 | Continuous hyperbolic pencil for all real s > 1 | REPAIR | Blocked | Repair printed real-s density normalization (factor π/2 discrepancy at odd weights); import/prove corrected continuous pencil and verify actual odd-s coincidence. |
| 7 | 3.3 | Total positivity, leading sign, universal signature | PARTIAL | Partially formalized | Complete *nonprincipal* mixed Hankel minors via Andreief/generalized Vandermonde and Carleman determinacy; sign parity and Sylvester root-side counts already proved locally. |
| 8 | 3.4 | Root interlacing and Dodgson condensation | PARTIAL / REPAIR | Blocked | Prove rank-aware Cauchy interlacing for compatible principal compressions and arbitrary-order Dodgson/Jacobi. Local principal-root reality already handles singular slopes; printed universal root counts need correction. |
| 9 | 3.5 | Stieltjes J-fraction from interlacing roots | REPAIR | Blocked | Derive a normalized J-fraction for `(I+tB)⁻¹`, restoring determinant factors; prove Lanczos cyclicity/no-breakdown or state the correct weaker result, and separate spectral edge growth. |
| 10 | 3.6 | Stieltjes reciprocal-root power sums | CORRECTED ONLY | Blocked | Printed all-order strict Hankel positivity and bound/sign conventions are false. Preserve the locally proved corrected finite-moment estimates and nearest-root convergence; prove only mathematically valid rank-sensitive statements. |
| 11 | 3.7 | Turanian non-negativity and Newton log-concavity | OPEN | Partially formalized | Build actual-family all-order Turan/Newton/equality proofs and avoid unjustified claims that intermediate centered coefficients never vanish. |
| 12 | 3.8 | Christoffel-Darboux pole representation and Jacobi derivative | NOT IN MAIN | Partially formalized | Actual Christoffel–Darboux evaluation at negative square poles plus justified Laplace-parameter differentiation/Jacobi trace identity. |
| 13 | 3.9 | Hurwitz and Dirichlet hyperbolicity | NOT IN MAIN | Partially formalized | Actual Hurwitz and Dirichlet positive kernel/measures at conductors 3,4,5,8; identify rational pole moments and conclude the concrete hyperbolicity pencil. |
| 14 | 4.1 | Spectral irrationality measure criterion | CONDITIONAL TRANSFER | Partially formalized | General conditional transfer is audited locally. Supply effective onset/rates for claimed computable threshold and real ζ(5) inputs; no automatic application from Theorem 3.1. |
| 15 | 4.2 | Transfer for algebraic approximations | NOT IN MAIN | Partially formalized | Import/audit algebraic resultants, conjugate heights, and degree-d selection/budgets for the real polynomial family. |
| 16 | 4.3 | Ultrametric zero-free disk | NOT IN MAIN | Already proved and retained | External repo has a full axiom-audited ultrametric-disk proof; migrate and independently check its exact statement in `snditeration`. |
| 17 | 4.4 | Spectral bound and irrationality measure for zeta(5) | NOT IN MAIN | Partially formalized | Construct actual integral normalization, p-adic integer multiplier, 0<\|Q_K(ζ(5))\|≤exp(-K²/2500), ‖B_K‖≤exp(11.411K), and effective rational exponent 25687. **Critical arithmetic bottleneck.** |
| 18 | 4.5 | Irrationality and measure for b*zeta(5)+a*zeta(3) | NOT IN MAIN | Partially formalized | Coupled ζ(5)/ζ(3) density positivity, aligned Z-slope, p-adic cancellation and uniform quantitative decay for bζ(5)+aζ(3). |
| 19 | 4.6 | Determinant bounds and coefficient heights | NOT IN MAIN | Partially formalized | Exact determinant normalization, asymptotic lower/upper log\|det B\| (0.23310, 3.73980) and coefficient height budgets; audit constants against printed paper. |
| 20 | 4.7 | Root collapse and separation | NOT IN MAIN | Partially formalized | Transfer spectral norm/determinant estimates to ≥1.40% exponentially clustered roots, gap and root separation for actual Q_K. |
| 21 | 4.8 | Rational root exclusion and cluster degree bounds | NOT IN MAIN | Partially formalized | Use family-specific nonvanishing, effective constants and heights to exclude rational roots with b≤exp(K/2251); prove factor-degree bounds. |
| 22 | 5.1 | Two-variable Beukers measure for zeta(7) | NOT IN MAIN | Partially formalized | Define/converge actual two-variable Beukers ζ(7) measure; prove diagonal ζ(7)-harmonic and off-diagonal rational moments. |
| 23 | 5.2 | Dual hyperbolicity and Krein decomposition | NOT IN MAIN | Partially formalized | Build actual dual positive-slope pencil, *infinite* Krein decomposition and tail-controlled cones; repair fixed-K subspace dimension quantifier. |
| 24 | 5.3 | Beukers measure and dual pencil for beta(4) | NOT IN MAIN | Partially formalized | Analogous genuine β(4) two-variable integral, moments and dual hyperbolic pencil. |
| 25 | 5.4 | Higher-zeta cancellation on even pole pairs | NOT IN MAIN | Verified | External repo has a fully audited even-pole cancellation theorem; import its corrected proof without copying its assertion as an axiom. |
| 26 | 5.6 | Weight-seven prime-sum evaluation and pole refinement | NOT IN MAIN | Not formalized | Prove eleven exact outer prime-sum affine pieces and integral 453803/288000; inner bound and pole-ordered gain require corrected endpoint/variance/survivor-class analysis. |
| 27 | 5.7 | Double-pole determinant for 1,zeta(5),zeta(6) | NOT IN MAIN | Not formalized | Prove actual double-pole decomposition, q-adic nonvanishing v_q(J_{2m})=-36m and explicit lower minor valuations. |
| 28 | 6.1 | Divided-difference valuation and intrinsic p^-6 barrier | NOT IN MAIN | Not formalized | Prove divided-difference prime valuation -7 and real two-variable→Mellin bridge, plus the intrinsic p^-6 obstruction. |
| 29 | 6.2 | Simultaneous weight-(6,7) Beukers functional | NOT IN MAIN | Partially formalized | Actual simultaneous ζ(6),ζ(7) Beukers integral/moments and zero-denominator arithmetic transfer. |
| 30 | 6.3 | q-adic nonvanishing and positive-cone approximations | NOT IN MAIN | Blocked | Printed positive-cone assertion (part 2) is counterexampled externally at h=4; replace cone/tail control. Part 1 q-adic nonvanishing remains independent and open. |
| 31 | 6.4 | Character-Vandermonde sign cancellation and beta hyperbolicity | NOT IN MAIN | Partially formalized | Actual character–Vandermonde residue sign cancellation; β(2k) positive spectral pencil and q-adic nonvanishing. |
| 32 | 6.5 | q-adic nonvanishing at zero | NOT IN MAIN | Not formalized | Exact q≡1 mod 8 valuation v_q(Δ_K(0))=-(3m_q-2) including local block arithmetic. |
| 33 | 6.6 | Generalized multi-weight positive-definite pencil | NOT IN MAIN | Partially formalized | Actual multiweight density, uniform comparison, positive-definite pencil, signature and p-adic integrality. |
| 34 | 6.7 | Universal multi-weight Beukers Krein decomposition | NOT IN MAIN | Not formalized | Genuine universal multiweight two-variable measure, infinite Krein spaces and q-adic nonvanishing; finite signed Gram algebra does not suffice. |
| 35 | 6.8 | Three-term linear-independence cone | NOT IN MAIN | Not formalized | Construct full arithmetic three-term linear forms and nonvanishing/height/decay to conclude independence of 1,ζ(3),ζ(5). |
| 36 | 6.9 | Triple-pole and multi-weight determinants | NOT IN MAIN | Partially formalized | Actual triple-pole Hermite table, global pole order, invertible local block and q-adic determinant transfer. |
| 37 | 6.10 | Potential-gap identity and quadratic derivative growth | NOT IN MAIN | Partially formalized | Family-specific one-/two-variable potential-gap identity and quadratic-rate asymptotics, not merely finite Gram algebra. |
| 38 | 6.11 | Distribution growth and 2-adic quotient obstruction | NOT IN MAIN | Not formalized | Euler distribution, prime weights and 2-adic quotient-leading-term obstruction with parameter growth. |
| 39 | 6.12 | Full-dimension sign-flip positivity and q-adic nonvanishing | NOT IN MAIN | Not formalized | Actual full-dimension sign-flipped Gram positivity, rational cutoff near sign switch and q-adic nonvanishing. |
| 40 | 6.13 | Central-factorial secant differential identity | NOT IN MAIN | Blocked | Correct printed central-factorial series sign, justify differentiated infinite series and actual β-pencils/signature/Newton consequences. |
| 41 | 6.14 | Even-pole cosh scaling and coupled pencils | NOT IN MAIN | Not formalized | Even-pole cosh/Beta moments and uniform comparison constants leading to quantitative coupled spectral disks. |
| 42 | 6.15 | Arithmetic transcendence, positive measure and rank-one law | NOT IN MAIN | Blocked | Repair false printed h^(-2k) exterior asymptotic; effective transcendence, rank-one positive measure and strict positivity need new work. |
| 43 | 6.16 | Generalized multi-weight Zeta-Beta pencil | NOT IN MAIN | Not formalized | Construct infinite combined ζ/β density, its actual moment pencil and positivity/arithmetic cone, not only finite cone algebra. |
| 44 | 6.17 | Universal two-variable Zeta-Beta pencil | NOT IN MAIN | Partially formalized | Correct odd-pole congruence classes and construct genuine coupled ζ/β Beukers measure, infinite Krein and nonzero highest-weight local block. |
| 45 | 6.18 | Principal-minor 2-adic integrality and dyadic heights | NOT IN MAIN | Partially formalized | Full dyadic principal-minor integrality, odd-prime multiplier, determinant-height loss, and final explicit irrationality measure. |

## Decisive proof dependencies (not a list of Lean filenames)

### A. Structural / spectral closure
1. **Lemma 2.3, derivative at zero.** Under the proved regularity hypothesis `(RatFunc.denom f).eval 0 ≠ 0`, identify the algebraically defined `partialFractionCoefficient (2*k) f` with the actual `iteratedDeriv (2*k) (fun x : ℝ => RatFunc.eval (Rat.castHom ℝ) x f) 0 / ((2*k).factorial : ℝ)`. Prove on polynomial and nonzero simple-pole generators, preserve rational-function equality near zero, then extend linearly. Reuse the exact local `RationalDifference` and `RationalRegularity`; do not postulate smoothness at a pole.
2. **Theorem 3.3(1), continuous mixed minors and determinacy.** Positive-definiteness of every principal Gram restriction and exact inertia are already audited. The missing theorem is *strict positivity for nonprincipal minors* via Andreief and ordered generalized Vandermonde signs, with justified moment growth/Carleman divergence.
3. **Theorem 3.4, corrected rank-sensitive interlacing.** Build one Cholesky normalization compatible across leading principal submatrices, prove Cauchy eigenvalue interlacing with potentially zero slope eigenvalues, transfer reciprocals separately on positive/negative spectra, and prove all-order Dodgson/Jacobi. Never enumerate r finite roots without proving rank r.
4. **Corollaries 3.5–3.6 and Theorem 3.7.** Use the correct resolvent normalization and finite-atom rank; prove valid corrected Lanczos/no-breakdown hypotheses and Turan/Newton equality cases. Distinct roots alone do not imply coefficient nonvanishing.
5. **Theorems 3.8–3.9.** Bridge abstract kernel and finite pencil algebra to the actual Christoffel–Darboux/Laplace family and the explicit Hurwitz/character measures. These are not consequences of an arbitrary positive matrix pencil.

### B. Quantitative / arithmetic closure
6. **Theorem 4.4 is the decisive ζ(5) bottleneck.** Need a concrete integer-valued polynomial family `Q_K`, effective multiplier/denominators, `0 < |Q_K(ζ(5))| ≤ exp(-K²/2500)` for large admissible `K`, and `‖B_K‖ ≤ exp(11.411 K)`; only then can the conditional rational-transfer theorem deliver the printed `25687` exponent. Formalize the residue-factorial potential and the Legendre/Remez enclosure with a certified maximum, rather than accepting a numerical decimal or an unpublished estimate.
7. **Theorems 4.5–4.8.** Deduce coupled linear-form positivity, p-adic integrality, determinant/height bounds, root clustering and rational-root exclusion from verified *actual-family* constants. The auxiliary conditional transfer or spectral reality alone is insufficient.
8. **Proposition 4.3 and Theorem 5.4 have completed external proofs.** Favor commit-pinned selective migration into `snditeration`, then require its own full compiler+transitive axiom audit before marking either local PASS.

### C. ζ(7), Beukers, β and multiweight
9. **5.1–5.3:** construct the true two-variable integral and all moments, not just rational coefficient Gram matrices; prove infinite Krein identities and control discarded tails.
10. **5.6:** formally derive the eleven affine floor-function intervals and exact `453803/288000` integral. The external review documents false endpoint continuity, a 25→16 variance-coefficient repair, and an invalid universal survivor-pole `+6` argument. The inner prime bound and valuation improvement require a fresh family-specific proof.
11. **5.7, 6.1–6.18:** separate true p/q-adic local nonvanishing from analytic infinite-family positivity, effective height/decay, and multiweight transfer. The externally diagnosed `6.3(2)` positivity assertion is refuted by a rational/analytic `h=4` certificate, which is **not yet a Lean kernel proof**. Printed `6.13` series sign and `6.15` exterior asymptotic also require correction.

## Execution queue and measurable acceptance

| Priority | Deliverable | Acceptance criterion |
|:---|:---|:---|
| P0 | Preserve baseline and classify false print | No changed frozen `.lean` files; printed vs corrected statements linked separately |
| P1 | Lemma 2.3 derivative bridge | Actual RatFunc theorem compiled, named and transitive-axiom audited under local pinned Mathlib |
| P2 | 3.3 mixed minors + Carleman | Actual weight and generalized Vandermonde + all-order strict minor theorem; not only principal positivity |
| P3 | 3.4, 3.5, 3.6, 3.7 corrected spectral chain | Rank-sensitive interlacing, all-order Dodgson, normalized J-fraction, valid finite-rank moments, Turan equality proof |
| P4 | 3.8, 3.9, 4.2, 4.3, 5.4 cross-base intake | Literal actual-function statements mapped, imported without ad hoc axioms, passing new local audit |
| P5 | ζ(5) quantitative arithmetic 4.4–4.8 | Explicit multiplier, prime valuations, positive decay, spectral exponential bound, effective thresholds, claimed constants |
| P6 | ζ(7)/β two-variable Sections 5–6 | Actual infinite measure + tails + p-adic local blocks + corrected positivity/cones + full transfer |

## Updating this persistent branch

Keep this branch as **a tracker**, not an alternate math base. After each accepted native or CI Lean proof, update the affected row with (i) exact original paper clause, (ii) source module/fully qualified theorem, (iii) immutable commit and successful compiler/audit run, (iv) its stated hypotheses and which downstream conclusion actually follows, and (v) any remaining correction. If only a cross-branch theorem or failed candidate exists, leave the `snditeration/main` status unchanged. Do not promote a printed item based on file count or a similarly named lemma.

**No full Zetahyperbolic manuscript proof, unconditional ζ(5)/ζ(7) irrationality, or RH/finite-witness closure is certified by this tracker.**