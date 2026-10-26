# Zetahyperbolic — persistent paper-gap tracker for `snditeration`

## 1. Established proof-tier definitions

Canonical source: `YOU_ARE_GOODWORKFLOWFRONTIER_WORKFLOW_DEFINITION_v1_0_15`. These are **evidence gates**, not subjective priority rankings.

| Proof marker | Tier | Exact established criterion |
|---|---|---|
| `!` | **B-Tier** | An on-paper mathematical derivation conditional on reasoning; **not Lean-verified**. |
| `!!` | **A-Tier** | Exact Lean statement parsed, elaborated, compiled and transitively axiom-audited without `sorryAx`, custom/hidden axioms or unmentioned assumptions. The *proof may itself be explicitly conditional*; only its exact conclusion under stated hypotheses is certified. |
| `!!!` | **Formal closure** | An **A-Tier** conditional theorem chain reduces the desired final conclusion to acceptance of a finite witness by a terminating checker; **no concrete accepted witness yet**. This is **not** S-Tier. |
| `!!!!` | **S-Tier** | A concrete finite witness actually passes the terminating checker/admission, and a Lean-verified, axiom-audited downstream chain proves the final claimed conclusion. |

**Ordering:** `B-Tier → A-Tier → Formal closure → S-Tier`. The marker is assigned to a **specific proved statement**, not to the name of a manuscript section. A compiled conditional lemma or corrected replacement does **not** certify the stronger original printed theorem. `—` means no qualifying tier for the **whole printed statement** (even if there are partial or external components). The `!!` labels **subclaim**, **conditional** and **corrected** certify only those narrower exact Lean declarations. `cross-repo` means an audited proof exists at the pinned companion commit but has **not** been locally imported and rebuilt in `snditeration/main`.

**Separate workflow controls (not proof tiers):** `B_TIER_DERIVATION`, `A_TIER_EXECUTION`, `A_TIER_PLANNING`. Build name-tags `_construction`, `_subcritical`, `_critical` and `_reasonal_assertion` are progress/recheck labels, never proof certificates. **No item here meets `!!!` or `!!!!`;** no unconditional ζ(5)/ζ(7) irrationality or full-paper certification follows from the present receipts.

## 2. Manuscript items (45), in printed order

**Whole-item gate** and **component gate** are intentionally separate. A checkmark/strikethrough appears only for an exact original printed item with a passed Lean proof. A `!!` attached to a correction or subclaim certifies **only that narrower statement**, never the unresolved parent. The full [45-item tracker](docs/PAPER_GAP_TRACKER.md) gives source/CI and missing prerequisites.

| # | Printed item | Title | Whole-item proof tier | Separate verified component / status |
|---:|:---|:---|:---|:---|
| 1 | ~~2.2~~ ✓ | Rational functional pullback | `!!` **A-Tier original** | — (whole item completed) |
| 2 | ~~2.3~~ ✓ (local) | Reflection and difference identities for Tau | `!!` **A-Tier original** | `!!` Local canonical normalized analytic τ derivative, PR #18 CI PASS; totalized `RatFunc.eval` interoperability optional |
| 3 | ~~2.4~~ ✓ | Canonical basis invariance | `!!` **A-Tier original** | — (whole item completed) |
| 4 | ~~2.5~~ ✓ | Lagrange pole diagonalization | `!!` **A-Tier original** | — (whole item completed) |
| 5 | ~~3.1~~ ✓ | Universal hyperbolicity and zero-free disk | `!!` **A-Tier original** | — (whole item completed) |
| 6 | 3.2 | Continuous hyperbolic pencil for all real s > 1 | — **printed normalization false** | `!!` **corrected theorem only** |
| 7 | 3.3 | Total positivity, leading sign, universal signature | — **open as printed** | `!!` Actual **all principal** Gram minors and every strict 2×2 principal inequality; nonprincipal mixed minors and determinacy open |
| 8 | 3.4 | Root interlacing and Dodgson condensation | — **printed root-count requires repair** | `!!` A-Tier, **subclaim**; repair |
| 9 | 3.5 | Stieltjes J-fraction from interlacing roots | — **printed J-fraction false** | `!!` A-Tier, **subclaim**; repair |
| 10 | 3.6 | Stieltjes reciprocal-root power sums | — **printed all-order strictness false** | `!!` Corrected **weighted finite-atomic determinant iff order≤distinct support**; printed all-order positivity false |
| 11 | 3.7 | Turanian non-negativity and Newton log-concavity | — **open as printed** | `!!` LOCAL actual-family derivative Turán/strict centered Newton and no-consecutive-zero coefficients (PR #23); all-centered-individual-nonzero still open |
| 12 | 3.8 | Christoffel-Darboux pole representation and Jacobi derivative | — **open as printed** | `!!` Actual symmetric whitened/pole operator characteristic polynomial **and full root-multiset equality**; orthogonal CD kernel open |
| 13 | 3.9 | Hurwitz and Dirichlet hyperbolicity | — **open as printed** | `!!` A-Tier, **subclaim only** |
| 14 | 4.1 | Spectral irrationality measure criterion | — **open as printed** | `!!` Locally compiled conditional complex-root comparison, logarithmic index and effective-onset transfer (PRs #27/#28); actual ζ5 root gap and decay remain open |
| 15 | ~~4.2~~ ✓ (local) | Transfer for algebraic approximations | `!!` **A-Tier original (conditional)** | Exact conditional resultant/height transfer for all algebraic numbers of degree ≤d, including integer minimal-polynomial wrapper; PR #30 and local main CI PASS. **Family rate/separation inputs still open** |
| 16 | ~~4.3~~ ✓ (local) | Ultrametric zero-free disk | `!!` **A-Tier original** | `!!` **LOCAL certified**: exact ℂ_p norm-preserving disk, plus actual manuscript primitive-polynomial specialization; center nonvanishing remains the theorem hypothesis |
| 17 | 4.4 | Spectral bound and irrationality measure for zeta(5) | — **open as printed** | `!!` Positive primitive integer ζ5 polynomial, actual 30n family, finite pole-log and adjacent log-ratio identities; **uniform decay/multiplier missing** |
| 18 | 4.5 | Irrationality and measure for b*zeta(5)+a*zeta(3) | — **open as printed** | `!!` Finite positive determinant reweighting; coupled ζ5/ζ3 arithmetic open |
| 19 | 4.6 | Determinant bounds and coefficient heights | — **open as printed** | `!!` Exact original content–Gram/Vandermonde-pole log conservation; **K²-rate and direction repair open** |
| 20 | 4.7 | Root collapse and separation | — **open as printed** | `!!` Actual spectral exponent counting (cap/average conditional) and **large exponent ⇒ root within exp(-τ)**; K-uniform bounds open |
| 21 | 4.8 | Rational root exclusion and cluster degree bounds | — **open as printed** | `!!` A-Tier, **subclaim only** |
| 22 | ~~5.1~~ ✓ (local) | Two-variable Beukers measure for zeta(7) | `!!` **A-Tier original** | `!!` **LOCAL exact**: positive measurable Beukers ζ7 density, actual double-integral moments for all r,t including both printed cases; PR #24 (moment integral) and PR #26 (explicit offdiagonal rationality) CI PASS |
| 23 | 5.2 | Dual hyperbolicity and Krein decomposition | — **fixed-K cones impossible as stated** | `!!` LOCAL finite rational CCᵀ dual positive slope/degree h/all-real complex roots (PR #25); actual Beukers integral and infinite signed cone open |
| 24 | 5.3 | Beukers measure and dual pencil for beta(4) | — **open as printed** | `!!` A-Tier, **subclaim only** |
| 25 | ~~5.4~~ ✓ (local) | Higher-zeta cancellation on even pole pairs | `!!` **A-Tier original** | `!!` Local all-j even-pole cancellation including j=1 and finite linearity, PR #21 CI PASS 8773 jobs |
| 26 | 5.6 | Weight-seven prime-sum evaluation and pole refinement | — **open as printed** | `!!` Rational sign checks only; outer/inner integral and valuations open |
| 27 | 5.7 | Double-pole determinant for 1,zeta(5),zeta(6) | — **open as printed** | — **no verified positive subtheorem** |
| 28 | 6.1 | Divided-difference valuation and intrinsic p^-6 barrier | — **open as printed** | — **no verified positive subtheorem** |
| 29 | 6.2 | Simultaneous weight-(6,7) Beukers functional | — **open as printed** | `!!` A-Tier, **subclaim only** |
| 30 | 6.3 | q-adic nonvanishing and positive-cone approximations | — **printed cone contradicted externally** | — **no verified positive subtheorem** |
| 31 | 6.4 | Character-Vandermonde sign cancellation and beta hyperbolicity | — **open as printed** | `!!` Finite β character sign, 2-/3-node Gram; full analytic moments/q-adic bounds open |
| 32 | 6.5 | q-adic nonvanishing at zero | — **open as printed** | — **no verified positive subtheorem** |
| 33 | 6.6 | Generalized multi-weight positive-definite pencil | — **open as printed** | `!!` Conditional finite positive-weight matrix cone: real spectrum, weak/strict-off-roots Turán; infinite density/prime bounds open |
| 34 | 6.7 | Universal multi-weight Beukers Krein decomposition | — **open as printed** | — **no verified positive subtheorem** |
| 35 | 6.8 | Three-term linear-independence cone | — **open as printed** | — **no verified positive subtheorem** |
| 36 | 6.9 | Triple-pole and multi-weight determinants | — **open as printed** | `!!` A-Tier, **subclaim only** |
| 37 | 6.10 | Potential-gap identity and quadratic derivative growth | — **open as printed** | `!!` Finite K²-normalized potential and pole-energy identities; **asymptotic rate/gap open** |
| 38 | 6.11 | Distribution growth and 2-adic quotient obstruction | — **open as printed** | `!!` Elementary **odd-square scaling and consecutive-product parity**; Euler distribution/2-adic valuations open |
| 39 | 6.12 | Full-dimension sign-flip positivity and q-adic nonvanishing | — **open as printed** | — **no verified positive subtheorem** |
| 40 | 6.13 | Central-factorial secant differential identity | — **printed series sign incorrect** | `!!` A-Tier, **subclaim**; repair |
| 41 | 6.14 | Even-pole cosh scaling and coupled pencils | — **open as printed** | — **no verified positive subtheorem** |
| 42 | 6.15 | Arithmetic transcendence, positive measure and rank-one law | — **printed exterior-rate correction needed** | `!!` Qualitative odd-beta transcendence, exact k=0 π/4 and log2/2 moments and Mellin integrals; **η(1) removable endpoint and effective-rate repairs remain** |
| 43 | 6.16 | Generalized multi-weight Zeta-Beta pencil | — **open as printed** | — **no verified positive subtheorem** |
| 44 | 6.17 | Universal two-variable Zeta-Beta pencil | — **open as printed** | `!!` **Lean counterexamples to proof steps** |
| 45 | 6.18 | Principal-minor 2-adic integrality and dyadic heights | — **open as printed** | `!!` A-Tier, **subclaim only** |

**Totals:** Nine fully verified printed items as stated (including conditional Proposition 4.2) in the canonical repository (nine local, zero companion-only), **36 uncompleted or repair-required**; no paper-wide `!!!` or `!!!!`.

**Historical evidence-mining checkpoint (before P05.01 merge):** the whole-item count reached **7/45** early and has not increased over the repeated documentation rounds; unfinished rows with at least one certified supporting-claim marker grew **0 → 21 → 23 → 27 → 28** and then stabilized. The number of inline crossed phrases increased to **60**, but these phrases are **not** 60 independent or newly compiled Lean proofs. The indexed, hash-matched source-module coverage increased from 18 to **22**. The [historical convergence ledger](docs/CONVERGENCE_TRACKER.md) and [machine-readable 13-checkpoint series](docs/CONVERGENCE_HISTORY_2026-10-26.json) distinguish genuinely new mathematical evidence from reclassification and documentation saturation.

**Reinference signal:** `∅ REINFERENCE_NO_DELTA` and **`EVIDENCE_SATURATED_FIXED_SOURCE`** were established only **after** four previously existing source modules were newly catalogued and two subsequent, independent unchanged-source passes found zero additional certified theorem or changed mathematical blocker. [Read the bounded saturation receipt](docs/REINFERENCE_SATURATION_2026-10-26.md). This is a stopping rule for repeated cataloguing, not a claim that the manuscript is fully proved.

**Further five-round audit:** [26 October additional audited crossings](docs/ROUND_AUDIT_2026-10-26_ADDITIONAL_CROSSINGS.md) confirms actual primitive ζ5 positivity/unbounded indexing, the full finite 5.2(1) spectral clause, explicit negative/positive rational rank-one ζ7 channels, exact finite K² potential identities, β character parity and positive derivative reweighting. All remaining analytic and arithmetic conclusions stay open. No new Lean build receipt was claimed for this documentation update.

**Seven additional verification rounds:** [source-hashed machine-readable receipts](docs/CROSSINGS_MACHINE_2026-10-26.json) and [centered Taylor, pole-energy, dual-matrix and β(1) audit](docs/ROUND_AUDIT_2026-10-26_MOMENTS_AND_POLES.md). These newly crossed pieces are compiled, axiom-audited *subclaims*, not new complete manuscript items. They include the actual no-two-consecutive-zero Taylor theorem, exact finite pole-energy identities, the dual-pair discriminant criterion, weight-invariant dual slopes, the k=0 beta moment integrals and the η(1) removable-value correction.

**Six further source-level verification rounds:** [principal-versus-mixed minors, sharp finite-Hankel rank, symmetric pole spectra and dual S.O.S. sweep](docs/ROUND_AUDIT_2026-10-26_PRINCIPAL_MIXED_AND_DUAL.md). The tracker now explicitly crosses the **precise** principal Gram theorem, weighted rank threshold, root-multiset equality, finite signed-channel hypotheses, finite multiweight strict Turán and odd-square parity identities. Each remains separate from the unproved stronger analytic or arithmetic claim. The [machine-readable crossing ledger](docs/CROSSINGS_MACHINE_2026-10-26.json) records their pinned source hashes and passing module receipt.

**Latest six-round proof-source sweep:** [principal-versus-mixed minor positivity, the exact weighted finite-rank threshold, the symmetric pole root multiset, dual signed finite cones, and strict finite multiweight Turán](docs/ROUND_AUDIT_2026-10-26_PRINCIPAL_MIXED_AND_DUAL.md) are now individually crossed at the *subtheorem* level. The [machine-readable ledger](docs/CROSSINGS_MACHINE_2026-10-26.json) records **18 pinned, source-hashed, passing module entries**; this is neither a count of whole manuscript theorems nor evidence that the sources were newly compiled in this documentation turn.

**Reinference finding before saturation:** a new source-hash index now covers 22 pre-existing audited companion modules, including the actual 4.7 exponent-to-root transfer, 4.1 factor-two integer-polynomial comparison, 3.7 Rolle separation and 5.2 summable-mode Krein algebra. This is **newly catalogued evidence, not newly compiled Lean code**. Track no-delta passes separately using the convergence receipt.

### More completed subclaims uncovered in the 26 October repeat audit

The new passes verified the **rank-sensitive degree/root count** for every principal determinant in 3.4, **correct two-/three-level J-fraction continuants** in 3.5, plus precisely matched the all-order derivative Turán, weak/strict/equality Newton clauses of 3.7 and conditional degree-d algebraic transfer in 4.2. Exact q=11 and q=41 Lean calculations refute two **intermediate** 6.17 local-arithmetic proof steps without refuting its full hypothetical theorem.

The original PDF also contains an independently confirmed **inequality-direction gap in 4.6(2)**: a stated upper bound on `A_M` is used to infer a lower bound for a leading coefficient. A new lower-rate estimate is required; the previously identified reversed-root-gap argument in 4.8(1) is likewise still unproved.

[**26 October multi-round source audit**](docs/REPEAT_AUDIT_2026-10-26.md) · [**64 sub-obligation register**](docs/PAPER_GAP_REGISTER.md) · [25 October baseline](docs/MULTI_ROUND_CROSS_AUDIT_2026-10-25.md)

### Collected cross-project intake (26 October 2026)

The source collection has a [dedicated draft PR #16](https://github.com/randogelist/snditeration/pull/16) on branch `feat/zetahyperbolic-cross-project-intake-v1`. It pins **16 companion Lean sources** as inert `.lean.txt` snapshots, with source SHA-256 and a small-PR migration plan. The independent [source-packet merge matrix](docs/CROSS_PROJECT_SOURCE_INTAKE_20261026.md) identifies 10 targeted waves, checked source dependencies, the failed PR #15 salvage frontier and the warnings for conditional/axiom-dependent ZIP material. A separate downloadable user ZIP `ZETAHYPERBOLIC_CROSS_PROJECT_INTAKE_v0_1_2.zip` contains 30 inert data/source snapshots from 25 original archives.

**Local merger status:** `SRC_COLLECTED`, not `DEST_COMPILED`. The draft CI PASS (when present) means only that the unchanged imported Lean project still builds, because no `.lean.txt` snapshot enters the default import graph. A print-axioms check and exact paper-object adapter remain necessary before closing a local gap. Current completed printed total remains **7/45 across the two repositories**.

**P04.03 local A-Tier closure (26 October 2026):** [PR #17](https://github.com/randogelist/snditeration/pull/17) merged as `1e7d422c`; [8,765-job CI and exact axiom audit 40259783326](https://github.com/randogelist/snditeration/actions/runs/40259783326) passed. The three originally companion-only closures are now **0 local-import-pending** plus locally merged 4.3. The combined whole-item total remains 7/45. [Read the native project checkpoint](https://github.com/randogelist/snditeration/blob/main/docs/P04_03_NATIVE_CHECKPOINT.md). This new source commit ends the earlier **fixed-source** evidence-saturation interval.

**Integration ownership:** [Independent integration lane and noninterference protocol](docs/INTEGRATION_LANE.md) documents which development branches are protected, the single-target merge gate, and locally verified PR #19 (Mellin moments). It does not change the whole-item count of 7/45.

**Independent integration closure:** [PR #20](https://github.com/randogelist/snditeration/pull/20) merged the standalone Newton/Turán core from failed donor PR #15; [full Lean+axiom PR CI 40265147642](https://github.com/randogelist/snditeration/actions/runs/40265147642) passed. Seven exact axiom reports were standard-only; the source is identical to its donor. This is local A-Tier mathematical **support for printed 3.7**, not proof of the still-open individual centered-coefficient nonvanishing. The original complete printed theorem count remains 7/45.

**Independent local P03.02 support integration:** [PR #22](https://github.com/randogelist/snditeration/pull/22) merged corrected real-weight density and moments (two unchanged, previously individually built PR #15 sources); [CI 40265703589](https://github.com/randogelist/snditeration/actions/runs/40265703589) passed all eight targeted axiom checks. This is **A-Tier partial/corrected support**, *not* proof of the false-as-printed continuous pencil or a new complete manuscript item.

**P02.03 and P05.04 local closure (26 October 2026):** [PR #18](https://github.com/randogelist/snditeration/pull/18) (CI 40262441761) and [PR #21](https://github.com/randogelist/snditeration/pull/21) (CI 40265986335, 8,773 jobs, 1,011 audited project theorems) both merged into `main`, with their exact compiled theorem types and standard-only axioms. All seven original printed certified items are now **locally integrated**; the full manuscript remains **7/45**, and corrected/nonprinted stronger assertions are still separate.

**26 October local-integration freeze:** Lemma **2.3** ([PR #18, CI PASS](https://github.com/randogelist/snditeration/actions/runs/40262441761)), Proposition **4.3** ([PR #17, CI PASS](https://github.com/randogelist/snditeration/actions/runs/40259783326)), and Theorem **5.4** ([PR #21, CI PASS](https://github.com/randogelist/snditeration/actions/runs/40265986335)) are now all imported, compiled and axiom-audited in `snditeration/main`. Consequently **all seven previously certified complete printed items are now locally A-Tier**, with the aggregate 7/45 unchanged. Theorem 5.4 merged at `f64b49b9` with **8,773 jobs**, four standard-only targeted axiom prints and a PASS placeholder scanner. The next candidate is **Theorem 5.1** (actual two-variable ζ(7) moments), not started.

**Integration-lane closure:** [PR #23](https://github.com/randogelist/snditeration/pull/23) (actual Newton/Turán, merge `9f630aef`, [CI 40266691690](https://github.com/randogelist/snditeration/actions/runs/40266691690) and [main CI 40266911494](https://github.com/randogelist/snditeration/actions/runs/40266911494) PASS) and [PR #25](https://github.com/randogelist/snditeration/pull/25) (six-module finite dual spectrum, merge `484e285e`, [CI 40267266192](https://github.com/randogelist/snditeration/actions/runs/40267266192) and [main CI 40267527070](https://github.com/randogelist/snditeration/actions/runs/40267527070) PASS) are merged. Both are exact **supporting** A-Tier components; original full-item count stays **7/45**. The other agent’s active [5.1 PR #24](https://github.com/randogelist/snditeration/pull/24) remains untouched.

**NEW LOCAL A-TIER CLOSURE — Theorem 5.1 (26 October 2026):** actual two-variable positive Beukers density and the full diagonal/offdiagonal integral identities, including `ζ(7)-H_r^(7)`, `(H_r^(6)-H_t^(6))/(6(r-t))`, exact 720 normalization, summability and justified series–integral exchange. [PR #24](https://github.com/randogelist/snditeration/pull/24), [Lean 4.33 CI 40267850777](https://github.com/randogelist/snditeration/actions/runs/40267850777), 8,783 build jobs PASS, standard-only axioms, main `1ae34f2bc30135460c357f4efffe1fdbb93d5009`. The **current** exact original-paper total is **8/45, all eight certified locally**; the historic 7/45 source-mining convergence series below is a **past snapshot**, not the present count. Next possible single-target endpoint: Theorem 5.2(2), not yet started.

**P05.01 final local certification:** [PR #24](https://github.com/randogelist/snditeration/pull/24) proves the exact ζ(7) moment integral; [PR #26](https://github.com/randogelist/snditeration/pull/26) adds the explicit witness that every offdiagonal integral is a rational number. [CI 40267850777](https://github.com/randogelist/snditeration/actions/runs/40267850777) and [CI 40268502325](https://github.com/randogelist/snditeration/actions/runs/40268502325) both passed with standard-only transitive axioms (8,783 and 8,784 jobs). Frozen [main receipt](https://github.com/randogelist/snditeration/blob/main/docs/P05_01_A_TIER_RECEIPT.json). **8/45** original printed items now certified; Theorem 5.2(2) infinite Krein decomposition remains next and unstarted.

**P04.02 local exact conditional A-Tier closure (26 October 2026):** [PR #30](https://github.com/randogelist/snditeration/pull/30) merged as `7775f7daf2cfb15d7a7614fd30371cc7a1392aed`; [PR CI 40270563393](https://github.com/randogelist/snditeration/actions/runs/40270563393) and [post-merge main CI 40270854695](https://github.com/randogelist/snditeration/actions/runs/40270854695) **both PASS**. Seven donor source modules remain byte-identical and ten transitive axiom reports use only `propext`, `Classical.choice`, `Quot.sound`. The exact conditional printed algebraic-approximation theorem now includes its full minimal-polynomial/algebraic-number formulation. Its degree, quadratic decay, all-complex-root separation and height-limsup estimates remain **explicit hypotheses**, not results about the actual ζ(5) family.

## 3. Source provenance, outstanding endpoints and maintenance

**Purpose:** a permanent, source-linked inventory of what remains to formalize or repair in the supplied 52-page Zetahyperbolic manuscript. This is documentation, not a second Lean proof implementation. The companion status is *not* automatically imported into `snditeration/main`.

### What is already established in `snditeration`

The pinned [main checkpoint](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/CHECKPOINT.json) reports **846 audited Lean theorem declarations** (including generated declarations), with [passing CI](https://github.com/randogelist/snditeration/actions/runs/40186793090), Lean **4.33.0** and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. It includes substantial *actual-family* mathematics, not merely abstract theorem wrappers:

- Section 2: actual rational-function domains, pullback/reflection, finite-difference algebra, polynomial-basis transport, Lagrange pole diagonalization.
- Section 3: positive hyperbolic moment measure and exact Gram realization; **Theorem 3.1**'s unconditional real roots, primitive degree and sharp operator-norm zero-free disk; spectral inertia/sign parity and root-side counts; principal-root reality; corrected reciprocal-moment estimates and limit.
- Section 4: a proved **conditional arithmetic transfer**, not its actual-family growth/decay assumptions.

See [the frozen local proof ledger](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/docs/FORMALIZATION_LEDGER.md). These 846 declarations must not be mistaken for 846 complete printed results.

### Already crossed off — 8 of 45 complete printed items (aggregate)

The following have exact Lean proofs with passing build/transitive axiom evidence in **at least one** of the two repos:

| Crossed manuscript item | Verification | Remaining work |
|---|---|---|
| ~~Lemma 2.2~~ | **LOCAL PASS** (`snditeration/main`) | None for printed pullback |
| ~~Lemma 2.3~~ | **LOCAL PASS** (`snditeration/main`, PR #18) | Canonical all-regular-domain analytic derivative passed; Mathlib totalized `RatFunc.eval` compatibility remains an optional stronger bridge |
| ~~Theorem 2.4~~ | **LOCAL PASS** | None for canonical primitive basis invariance |
| ~~Theorem 2.5~~ | **LOCAL PASS** | None for Lagrange pole diagonalization |
| ~~Theorem 3.1~~ | **LOCAL PASS** | None for exact odd-weight hyperbolicity/sharp finite disk; this is **not** a quantitative ζ5 measure |
| ~~Proposition 4.3~~ | **LOCAL PASS** (`snditeration/main`, PR #17) | Exact `ℂ_p` norm-preserving disk and primitive-polynomial specialization compiled and audited |
| ~~Theorem 5.1~~ | **LOCAL PASS** (`snditeration/main`, PR #24) | Exact positive two-variable ζ(7) Beukers integral with diagonal/offdiagonal harmonic moments and 720 normalization; Theorem 5.2 remains separate |
| ~~Theorem 5.4~~ | **LOCAL PASS** (`snditeration/main`, PR #21) | Exact all-j cancellation, j=1 endpoint and finite rational linearity compiled/audited |

**Aggregate count:** 9/45 complete printed items as stated, comprising **9 certified locally, all previously companion-only proofs now integrated**. All eight are now local `snditeration/main` closures; `CROSS-REPO PASS` does **not** mean locally imported or recompiled.

**More work already finished at subclause level:** corrected Proposition 3.2; all-order Dodgson part of Theorem 3.4; corrected Corollary 3.6; strict Newton components of 3.7; effective *conditional* index selection with explicit onset; `CCᵀ` dual-pencil algebra; `6d_K^7` Beukers denominator; finite central-factorial identities; qualitative odd-beta transcendence; polynomial quotient-degree thresholds. **Do not** cross off their full original printed theorems. Full [source-level cross-branch resolution audit](docs/CROSS_BRANCH_RESOLUTION_AUDIT_2026-10-25.md).

### Highest-priority missing pieces

| Priority | Exact unresolved paper endpoint | Concrete closure target |
|:---|:---|:---|
| P1 | **Lemma 2.3 optional interoperability** | Printed identity and canonical normalized analytic derivative already locally PASS. Optional proof: eventual equality with Mathlib's totalized `RatFunc.eval` at the origin. |
| P2 | **Theorem 3.3(1)** | All mixed Hankel minors strictly positive, plus the Carleman/Stieltjes determinacy proof; the sign/inertia clauses are already locally proved |
| P3 | **Theorem 3.4; Corollary 3.5; Theorem 3.7** | Rank-sensitive interlacing and corrected Lanczos fraction remain open. All-order Dodgson and the corrected finite-rank reciprocal-moment laws are audited elsewhere, but require local intake as applicable; full Newton/Turán endpoint remains open. |
| P4 | **Theorems 3.8–3.9; Proposition 4.2** | Complete Christoffel–Darboux/Hurwitz/character identification and algebraic transfer. Propositions 4.3 and Theorem 5.4 are now *locally* PASS and frozen. |
| P5 | **Theorems 4.4–4.8** | Real ζ(5) arithmetic multipliers and determinant decay, `‖B_K‖ ≤ exp(11.411 K)`, height/prime estimates, the asserted irrationality exponent **25687** and linear-form transfer |
| P6 | **Sections 5–6** | Actual ζ(7)/β Beukers integrals, infinite Krein/tail bounds, prime sums, double/triple pole valuations, multiweight positivity and arithmetic conclusions |

**Do not try to prove the literally false printed clauses unchanged.** The audit flags: the continuous-density normalization in 3.2; the unnormalized J-fraction in 3.5; all-order strict finite-atomic Hankel positivity / reversed estimate in 3.6; unjustified coefficient-nonvanishing in 3.7; and more serious proposed repairs for 5.6, 6.3, 6.13 and 6.15. The full register separates *proved counterexamples, suspected argument gaps, corrected variants and open theorems*.

### Cross-branch intake is useful, not automatic proof

The independent [Leaned Paper repository](https://github.com/randogelist/zetahyperbolic-axiom) reports a [passing 219-module audit](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) and **7 complete, 21 partial, 10 not formalized, 7 blocked** printed items. Its completed 4.3 and 5.4 and Section 2/3/4 developments are promising selective imports; **none is automatically certified in `snditeration`**. The wide [`feat/zetahyperbolic-continuation-20261025`](https://github.com/randogelist/snditeration/tree/feat/zetahyperbolic-continuation-20261025) supplies 51 changed candidate Section 2–6 files but [failed CI](https://github.com/randogelist/snditeration/actions/runs/40188938699) and cannot be credited as A-Tier.

### How this branch stays persistent

Update [the gap ledger](docs/PAPER_GAP_TRACKER.md) after every accepted proof, with **the literal manuscript statement, exact Lean declaration, source commit, compiler/axiom-audit receipt, hypotheses and what remains**. Freeze already proved modules unless their source or dependencies change. Track source integration, compiled lemmas, whole printed theorems and corrected statements separately. Keep historical ZIP archives unchanged.

#### Running the underlying Lean project

The active code remains on [`main`](https://github.com/randogelist/snditeration/tree/main). Use the installed Lean 4.33.0 and matching cached Mathlib to run `run.cmd` in the repository root, or `lake build Zetahyperbolic` followed by `lake env lean Zetahyperbolic/Audit.lean`. This documentation-only branch update does **not** claim a new compiler pass.

**Current manuscript completion: OPEN.** No unconditional irrationality of ζ(5) or ζ(7), RH, or S-Tier finite-witness admission is established here.
