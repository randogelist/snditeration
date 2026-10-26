# Cross-project source intake and ordered merge plan — 2026-10-26

## 1. Established proof-tier definitions

| Marker | Tier | Acceptance rule |
|---|---|---|
| ! | B-Tier | Paper derivation, no destination Lean certificate |
| !! | A-Tier | Exact theorem compiled in Lean and axiom-audited, no sorryAx/custom axioms/hidden premises |
| !!! | Formal closure | A-Tier chain reduces the specific target to a terminating finite checker, accepted witness outstanding |
| !!!! | S-Tier | Concrete finite witness admitted and downstream final theorem Lean-certified |

Reuse does not upgrade a theorem's tier until the exact destination statement, compiler and transitive axiom dependencies are checked. A proved conditional or corrected lemma is not the complete printed claim.

## 2. Collected source pools and their meaning

**Draft [PR #16](https://github.com/randogelist/snditeration/pull/16):** branch `feat/zetahyperbolic-cross-project-intake-v1`, base `snditeration/main@c521749`, commit `2d9fb68`. It contains 16 **inert** `.lean.txt` source snapshots from `zetahyperbolic-axiom/main@86ca99a`, all tied to their original source SHA-256 and the [219-module passing CI 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869). **No staged module is in the destination Lean import graph**, so draft CI green would not certify a new proof.

**User ZIP intake:** `ZETAHYPERBOLIC_CROSS_PROJECT_INTAKE_v0_1_2.zip`, SHA-256 `3982d2f1726ccfbae86f3bdcf436f1f8b3ee998bb9f450f20e629dd3c9cef118`. This has 30 original source/data snapshots gathered from the 25 uploaded archive ZIPs plus source/member SHA-256 provenance. It is **not yet stored in GitHub**, but delivered as a conversation artifact. Its data and research code have no new destination compiler receipts.

**Previous wide candidate [PR #15](https://github.com/randogelist/snditeration/pull/15):** source head `0cee4ea2`, [CI failure run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699). Review/build unaffected modules in independent PRs, not the entire failed import graph.

## 3. Actual gap-closing import waves

| Order | Current paper gap | Source intake / precise capability | Acceptance gate / unresolved premise |
|---|---|---|---|
| 1 / P0-C | **4.3** complete printed theorem **already proved in companion** | `Proposition_4_3_{PadicDisk,IsometricExtension,ComplexPadicDisk}` (3 modules in PR #16) | Rename/import under destination, compile and axiom-audit actual ℂp disk theorem. No K-family p-adic valuation claimed |
| 2 / P0-A+B | **2.3 and 5.4**, both complete **in companion** | `Section2DifferenceDerivative`, `Section2RatFuncTranslation`, `Section2TauLinear`, `Section2PoleLinearSpace`, etc. (6 snapshots) | Close full transitive rational-domain source dependencies and prove compatibility with destination actual Tau/partial-fraction types; j=1 normalization; compile and audit |
| 3 / P1 | **5.1**, the actual 2D ζ7 moment integral | `UnitLogMoments` (companion), `Zeta3Anchor.MomentSeriesTerm` and `MomentPartialFraction` (ZIP), `GP7` finite Laplace (ZIP), `CHEBYSHEV` native ζ7 eta (ZIP) | Prove exact change-of-variables `u=x1*x2`, Fubini/Tonelli, geometric series and `∫₀¹u^r(-log u)^m du=m!/(r+1)^(m+1)`; close (5.2) with 720 and divided differences. GP7/CHEB do not already prove (5.1) |
| 4 / P1 | **5.2(1–2)** finite dual and signed Krein representation | `Section5DualSpectrum`, `DualNullspace`, `KreinIdentity` (PR #16); generic 3×3 finite channel work in user ZIPs | Port already proved **finite** (1), then identify actual (5.1) kernel with summable infinite mode pairing; prove norm-tail controls before any polynomial ± cones |
| 5 / P1 | **3.3(1)** mixed minors + Carleman | `MomentGrowth`, `CarlemanDivergence`, `MixedMomentTwo`, `ShiftedMomentPositivity` in failed PR #15; positive measure theorem already in main | Isolate and repair `ShiftedMomentPositivity` (CI errors lines 86/128) then compile its dependents, use generalized Vandermonde/Andréief to bridge 2×2 to arbitrary mixed minors; prove Stieltjes moment determinacy separately |
| 6 / P1 | **3.4(1)** rank-aware Cauchy interlacing | `CauchyInterlacing`, `SignatureRestriction`, `PrincipalDegreeLoss` in failed PR #15; companion's audited rank-sensitive polynomial theorem | Repair actual count-interlacing proof in new branch (CI error lines 33/140+), handle singular principal slopes and reciprocal-root geometry. Do not assume every principal minor degree equals its matrix size |
| 7 / P1 | **3.8** actual CD/Jacobi deformation | `LaplaceMomentDerivative`, `LaplaceWeightDerivative`, `LaplaceGramMeasure`, `MatrixCurveJacobi`, `ChristoffelDarboux` in PR #15; GP7 Laplace source; companion `UnitLogMoments` | Fix Lean failures (weight derivative 37/46/48, curve Jacobi 145, CD 103/118+), establish actual moment integrability/differentiation and orthogonal-polynomial kernel |
| 8 / P1 | **4.1, 4.2, 4.7** exact local transfer frontiers | `Section4ComplexComparison`, `Section4ManuscriptBridge` and algebraic-transfer companion modules; many related PR #15 modules individually build | Transport full complex-root comparison under separation, and actual spectral exponent to root proximity, but actual asymptotic ζ5 root-cap/height inputs remain open |
| 9 / P2 | **4.8** finite denominator certificates | 3 R2 ζ5 candidate polynomials/exact intervals in user ZIP, plus `Zeta3R2Finite` Euler row mass and IMPACTG finite eta-source | Design terminating Lean rational checker, verify native ζ5 interval vs generated data. Exclusions up to B=27,65,145 are finite **external** claims and for **different R2 parameters**; not a proof of (4.8) for original K=30n |
| 10 / P2 | **5.6 / 6.2 / 5.7** q-adic prime/cancellation and rational denominators | `Zeta3Anchor.MomentArithmetic`, `Classifier64.Beukers`, CHEB η and GP7 finite Laplace, older `zeta5-spectral-lean` arithmetic | These are **templates only**, not target statements. Rebuild the original 3/40,37/40 ζ7 prime integrals and K30n ζ5 multiplier with exact interval/p-adic certificates. Never import axiom-contaminated Lean4.34 upstream blindly |

### Byte-identity deduplication of the 25 historical ZIPs

An exact SHA-256 sweep of all original user ZIP members found **810 `.lean` occurrences**, but only **541 distinct Lean source byte sequences**. The remaining **269 occurrences are exact duplicate source bytes**, and **158 distinct source hashes** occur across more than one archive. These are *source-file duplicates*, not theorems, proofs or independent confirmations. For example, the file named `Theorem_5_1_Two_Variable_Beukers_Measure_For_Zeta_7.lean` occurs byte-identically in five archives; that repetition does not prove its analytical content. Another duplicated candidate is `Theorem_6_3_Unconditional_Q_Adic_Non_Vanishing_And_Explicit_Positive_Cone_Approximations_For_G_A_7.lean`, also found in five archives despite the printed cone counterexample.

**Practical rule:** a future merge should compare source SHA-256 first, reuse a single canonical byte-identical source, and inspect exact theorem *types* and transitive axioms separately. Do not count each ZIP occurrence as a new mathematical result or compiler PASS.

## 4. What cannot be closed by source merging

- **4.4 ζ5 measure:** the printed family is `K=30n,N=3n,m=3`, and its crucial explicit multiplier/prime allocation, positive primitive value with *quadratic decay*, and operator norm bound remain unproved. Generic rational-polynomial estimates, finite witness candidates, and the separate Fauzan family do not discharge these actual-family inequalities.
- **5.2(3) and 6.3(2):** finite Krein Gram algebra is insufficient for an infinite signed kernel. The printed 6.3(2) positive cone has an external exact rational h=4 negative-direction counterexample; formulate a corrected theorem before attempting another formalization.
- **6.15:** qualitative odd-beta transcendence and k=0 moments already in companion do not imply the printed effective rate or false exterior asymptotics.
- **RH, QQRH, GP-KQ-BKQR, CHEB and classifier packets:** general proof checker and analytic architecture may transfer, but none of those arbitrary domains supplies a direct manuscript theorem without an exact actual zeta/Hankel bridge and new uniform estimates.
- **zeta5-spectral-lean:** bare `Zeta5.Axioms.chebyshev_theta_asymptotic`, Lean4.34 metadata and family mismatch mandate **research/quarantine only** until axiom-free 4.33 translation; standard-axiom audit required.

## 5. Repeatable intake receipt for every later merge

`SOURCE_ARCHIVE_OR_GITHUB_SHA=...`
`SOURCE_FILE_SHA256=...`
`THEOREM_FQN_AND_FULL_TYPE=...`
`SOURCE_TOOLCHAIN_MATHLIB=...`
`DEST_COMPILER_AND_MATHLIB=Lean4.33.0+db584cd6...`
`DEST_IMPORT_CLOSURE=COMPLETE|INCOMPLETE`
`DEST_BUILD=PASS|FAIL|NOT_RUN`
`PRINT_AXIOMS=PASS|FAIL|NOT_RUN`
`MANUSCRIPT_EQUIVALENCE=EXACT|SUBCLAUSE|CORRECTED|CONDITIONAL|NO`
`PAPER_GAP_ID=P...`
`MERGE_ADMISSIBLE=YES|NO`

**Status:** sources collected for future small PRs; **no new proof imported into main**, no extra whole printed item proved. Current combined exact original-item certification remains 7/45.
