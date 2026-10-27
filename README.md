# Zetahyperbolic — manuscript completion and Lean evidence

Formalization of *Spectral Theory and Diophantine Bounds for Hankel Determinants
of Odd Zeta Values* (Prince Anand, 21 October 2026; supplied 52-page manuscript),
using Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Workflow: `YOU_ARE_GOODWORKFLOWFRONTIER`; proof mode and execution target unchanged.

**Current main integration: 9 of 45 numbered proof statements have exact whole-statement
A-Tier evidence.** Proposition 3.2 has a complete **corrected** proof and is counted
separately. Other items contain useful verified components, source candidates,
open hypotheses, or printed claims requiring repair. These counts are an
inventory, not a percentage of mathematical work completed. No unconditional
ζ(5)/ζ(7) irrationality, RH, finite-witness closure, or full-paper completion is claimed.

## Evidence watch — 28 October 2026

**Active user focus: Chapter 3.** The historical Chapter 6 campaign below remains preserved.
Chapter 3 retains **3/9 whole originals in verified PR39 source (3.1, 3.3, 3.8)**,
**1/9 integrated on main**, and corrected 3.2/3.6 separately.
Next unrefuted original: **3.7**, requiring nonvanishing of every intermediate
centered coefficient for the actual family. The false degree clause of 3.4 needs
a separately stated correction; 3.5 needs normalized cyclic/no-breakdown and
spectral-edge statements; 3.9 needs actual Hurwitz/Dirichlet moment identification
and positivity. No new Chapter 3 completion is asserted.

Destination PR39 remains open at `3989d955e6190ab8fabc0720fad136b7e265e074`;
its already-recorded [successful run 40343849640](https://github.com/randogelist/snditeration/actions/runs/40343849640)
is still the latest destination run. Whole-original counts remain **13/45 verified
in PR sources; 9/45 integrated on main**. No new proof tier is granted.

Companion [PR51](https://github.com/randogelist/zetahyperbolic-axiom/pull/51)
is open at [`9adef7299961`](https://github.com/randogelist/zetahyperbolic-axiom/tree/9adef72999618ac4e63783ee8e2bff27dbcdd65d),
one commit beyond companion main `b56c8102d25b931a601992c93bf30b19cc7ee103`.
[Run 40345952106](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40345952106),
[job 121652794270](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40345952106/job/121652794270),
failed all five added modules: `ActualMixedAndreief`, `ActualMixedTwoMinors`,
`Section4RootMean`, `BetaOddMeasureActual`, and `CentralFactorialSeries`.
The log's `SUBSET_AXIOM_AUDIT=PASS` does **not** certify these failed modules or
the enlarged import graph. Elaboration-error output for `mixed_andreief` includes
`sorryAx`; it is not an accepted proof. These remain source candidates with failed
compiler evidence, not new certified components or destination integration.
Historical successful companion receipts remain intact.

The refreshed inventory contains **110 destination branches and 13 companion
branches**. All **108 experimental heads** exactly match their immutable
publication commits; the 72 PROP/ALT registrations, 51 prerequisite axioms and
consumption/compatibility gates are unchanged. The companion archive ref remains
`a241aa883da18eb1eb3ec027cbb971694bc7e3bf`; archive-source claims in PR51's
documentation do not confer certification on its failed new modules.
No proof source, branch target, mode/target lock or historical receipt is changed.

## Chapter 6 proof campaign — verified clauses and explicit repairs

**New exact clauses `!!`: 6.3(1), 6.7(1), and all of 6.10(2).** Further verified results cover the finite odd-square beta pencil, corrected secant Gram positivity in every order, the odd-beta rational root and its convergence, and repaired prime-cutoff estimates. New refutations identify fixed-degree cone, odd-prime-unit and unrestricted harmonic-bound errors. The h=4 counterexample to 6.3(2) was independently replayed with exact fractions; that replay is separate from Lean certification.

Source [`3989d955e619`](https://github.com/randogelist/snditeration/commit/3989d955e6190ab8fabc0720fad136b7e265e074) passed [CI 40343849640](https://github.com/randogelist/snditeration/actions/runs/40343849640): **190 library modules, 2,779 theorem declarations / 3,319 declarations**, inspected transitively with only `propext`, `Classical.choice`, `Quot.sound`. All 21 new modules are imported; earlier 169 library files, pinned dependencies/toolchain and workflow are unchanged. [Complete chapter register, proof outlines and repair gates](docs/CHAPTER_6_PROGRESS.md) · [immutable receipt](docs/receipts/CHAPTER_6_20261026.json).

**Whole Chapter 6 is not proved.** It contains false printed clauses and open arithmetic premises; 6.8 in particular still requires the missing ζ(5) irrationality argument. Whole-original totals remain **13/45 in verified PR source and 9/45 integrated on main**. Chapter 6 has **one complete original, 6.2**; corrected 6.1 is separate. The next independent chapter endpoint is **6.5**, with actual Lagrange-unit and determinant bridges still required. PR39 remains unmerged.

## Earlier companion observation — 26 October 2026

The following observation was published in main `9613480b439f5d90c450916ab32067a4d5e8fb35` before the destination verification above. Its companion receipts remain intact; its pending destination status is historical.

**6.3(1): companion component `!!`; destination transfer not yet certified.**
For every prime q≥5, the actual rows A_r(x)=x^r+x^(r+q), 0≤r<q,
give determinant valuation −7q at zero and at every rational a/b with q∤b.
The coefficient identification, four actual moments, slope 2I and determinant
evaluation bridge are proved, with no assumed local determinant conclusion.
[Exact source](https://github.com/randogelist/zetahyperbolic-axiom/blob/cdcb1935aa73a7c7e65006c1c198d114e9dcc6db/src/LeanPaper/BeukersPrimeMatrix.lean)
passed [CI 40339809027](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40339809027),
job 121631103447: 263 modules; 3,162 theorems / 3,901 project declarations
in the transitive audit, using only `propext`, `Classical.choice`, `Quot.sound`.
The module is explicitly imported and included in the all-project audit.
[Audit log](https://github.com/randogelist/zetahyperbolic-axiom/blob/b56c8102d25b931a601992c93bf30b19cc7ee103/validation/github/20261026-prime/kernel-audit.log)
and [source/dependency receipt](https://github.com/randogelist/zetahyperbolic-axiom/blob/b56c8102d25b931a601992c93bf30b19cc7ee103/validation/github/20261026-prime/acceptance.json)
remain in the companion repository. Companion PRs #49 and #50 are merged;
its main is `b56c8102d25b931a601992c93bf30b19cc7ee103`, differing from the
tested `cdcb1935aa73a7c7e65006c1c198d114e9dcc6db` only in documentation/receipts.

The printed intermediate integral-remainder congruence is false at q=7,r=0;
the proof uses the sufficient normalized remainder of q-adic norm <1.
This repairs the proof, without weakening the part (1) conclusion.
**Whole 6.3 remains unresolved:** part (2)'s prescribed positive-cone construction
still requires correction and valid tail control. No whole-original count changes:
**13/45 verified on historical PR39 sources; 9/45 integrated into destination main.**

Destination PR39 remains open and unmerged. Its later source
`009c368e189be6924d23e56643eff008826b7907` failed
[run 40342577767](https://github.com/randogelist/snditeration/actions/runs/40342577767)
before the audit and placeholder scan. Failures include beta root convergence,
partial fractions, pole norms, scaled units and polynomial integrality.
New Chapter 6 source candidates receive no certification from this failed run.
Earlier successful immutable certificates remain valid for their recorded states.

The active user focus is Chapter 6. Next gates are destination build/audit of the
new candidates and exact scope checks; 6.3(2)'s cone repair and 6.8's missing
arithmetic/decay inputs remain mathematical obstacles. The broader register's
next unrefuted original, 3.7, still needs actual centered-coefficient nonvanishing.
All 108 experimental heads match their publication receipts: 110 destination
branches and 12 companion branches were observed. The 72 paired attempts retain
their source-only status; no experimental assumption discharge or bridge is inferred.

## Focused result: Theorem 6.1 — corrected completion

**6.1(1) and 6.1(2) are exact original proofs; corrected 6.1(3) is complete, all `!!`.**
[Source `e56da14673218911252b92790d5fe713aea66e19`](https://github.com/randogelist/snditeration/tree/e56da14673218911252b92790d5fe713aea66e19)
passed [CI 40336562797](https://github.com/randogelist/snditeration/actions/runs/40336562797): **8,876 build jobs**, **169 library modules**,
**2,422 theorems / 2,886 declarations** audited transitively using only
`propext`, `Classical.choice`, and `Quot.sound`. Source-placeholder checks passed.
The tested merge has identical proof, dependency, toolchain and workflow sources;
only documentation differs.

The proof includes arbitrary rational-polynomial Mellin fibers against the actual
Beukers measure and the Jacobian; all outer-window harmonic lower bounds and exact
off-diagonal valuation -7; the actual local block at every p-integral p-adic X,
its printed scaled residue matrix, determinant norm p^14, and seventh-order pole
persistence for every primitive integral coefficient vector. The local block is
explicitly identified with the existing monomial affine pencil.

**Required correction:** the printed “no nonzero integral combination” is false.
The nonzero vector (p,0) lowers the pole to order at most six. The valid theorem
excludes **primitive** vectors, with at least one coefficient a unit; this
correction and the actual counterexample are both formally proved.
The complete corrected theorem therefore does **not** increase the **13/45**
original count or **9/45** main integration count. No global impossibility claim
for other constructions follows from this local obstruction.

[Correction log](docs/THEOREM_6_1_CORRECTIONS.md) ·
[immutable receipt and fingerprints](docs/receipts/THEOREM_6_1_20261026.json) ·
[full compiler/audit log](docs/receipts/THEOREM_6_1_CI_40336562797.log).
Proofs remain on open PR #39; no branch was merged or deleted.

## Verified repair branch — later evidence, not main integration

[PR #39](https://github.com/randogelist/snditeration/pull/39) is verified at
[`0672896955e5`](https://github.com/randogelist/snditeration/tree/0672896955e5dc7f7f9b9a0f5340c59e69f0890b).
[CI 40331258877](https://github.com/randogelist/snditeration/actions/runs/40331258877) passed
the full root build (8,864 build jobs), the transitive axiom audit of
**2,735 declarations / 2,282 theorems**, and the source-placeholder scan.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Every library module is
in the tested graph; no experimental module is imported.

**Verified source progress: 13/45 whole originals; integrated main: 9/45.**
The new whole originals are **3.3**, **3.8**, **5.3** and **6.2**. The transferred 5.3 proof uses the actual beta(4) measure; 6.2 proves the exact zeta(6)/zeta(7) functional and denominator clearing. The branch also completes corrected
3.6 and exact 5.2(1),(2); proves the actual all-k beta moments, arbitrary mixed
minors and rank-one slope; and formalizes the fixed-K cone obstruction, uniform
triple-pole cancellation and corrected odd-harmonic support.

Proof sources stay on the unmerged branch under the existing lock. Main receives
documentation only. The [earlier transfer receipt](docs/receipts/COMPLETION_20261026_TRANSFER.json) supplements the immutable
[CI7 receipt](docs/receipts/COMPLETION_20261026.json) and [CI15 continuation receipt](docs/receipts/COMPLETION_20261026_CONTINUATION.json), with native Windows and
companion evidence kept separate. See the [correction log](docs/FORMALIZATION_CORRECTIONS.md),
[45-item status inventory](docs/FORMALIZATION_STATUS.json) and
[source/import inventory](docs/FORMALIZATION_SOURCE_INVENTORY.json).

The first unresolved numbered original is **3.4**, whose full-degree clause is
false. The next unrefuted open original is **3.7**: individual centered-coefficient
nonvanishing for the actual family. Later arithmetic and asymptotic premises
remain explicit. No local Lean was executed; no target was replaced by an axiom.

## Unverified continuation — 26 October 2026

The [earlier candidate inspection](docs/receipts/CONTINUATION_OBSERVATION_20261026.md)
from concurrent main commit 1273af83a8d7 is preserved separately. Its pending/failed
states do not override the later successful certificates above.

## Chain categorizer and iterations

The [chain categorizer](docs/CHAIN_CATALOG.md) groups all **45 proof items** by
**chapter → item → subpart → PROP/ALT → iteration**. Its initial registration
contains the **72 existing paired attempts**; it creates no new research branch.

Each part can have multiple competing or successive iterations, such as
`P03_04.whole.alt.i0001`, then `P03_04.whole.alt.i0002`. Existing branch names
remain unchanged. New iterations record their own target, immutable source,
parents, dependencies, status and evidence. Newest does not mean selected,
superseded or proved; replacing an input still requires a compatibility proof.

Use [the guide](docs/CHAIN_CATALOG_GUIDE.md) and
[`tools/chain_catalog.py`](tools/chain_catalog.py) to filter, validate, register
another iteration and regenerate the table. The
[JSON catalog](docs/CHAIN_CATALOG.json) is the editable source; the older
[experiment manifest](docs/EXPERIMENTS.json) retains its publication receipts.
The categorizer neither executes Lean nor changes mathematical proof tiers.

## Dual proposed and alternative chains

Each of the **36 original items unfinished at publication** has two research branches:

| Role | Branch suffix | Purpose | Current publication status |
| --- | --- | --- | --- |
| PROP | `_prop_construction` | Preserve the original target and its explicit prerequisite interfaces. | Source-only, uncompiled; original assumptions unchanged. |
| ALT | `_alt_construction` | Develop a separately stated correction, restricted result, conditional result or alternative proof route. | Documentation-only candidate; typed ALT interfaces and new proofs are not yet supplied. |

The [paired branch index](docs/EXPERIMENTS.md#dual-chain-pairs) links all **36 pairs
(72 branches)**. The original **36 `_construction` branches** and their immutable
publication receipts are retained, giving **109 live branches including main** at
publication. The **51 unique named prerequisite axioms** belong to the original
scaffolds and are inherited unchanged by PROP; this step adds **no new axioms**.
ALT branches start from the main snapshot and do not copy the PROP experimental
axioms. No certified import graph or proof source is changed.

An ALT result does **not** automatically replace its PROP counterpart. Every
consumer needs an explicit proof that the selected alternative supplies its exact
input, or an explicitly revised consumer statement. A restricted result cannot
silently discharge the stronger original premise. Dependencies, repairs and open
obligations are recorded per alternative; none is guaranteed to close the chain.
Corrected 3.2 retains its historical corrected proof separately from the false
literal normalization. **That publication retained the then-current 9/45 exact-original count.**

Publication verification checked all **72 new heads and 144 documentation blobs**,
with only intended documentation changes relative to each recorded parent.
This is source identity, not Lean compilation or theorem certification. See the
[dual-chain policy](docs/EXPERIMENTAL_AXIOM_POLICY.md) and
[machine-readable index](docs/EXPERIMENTS.json). Historical snapshot records below
and in the manifest remain intact.

## Evidence snapshot

- Source reviewed: [`main@3b184ba109f065d973957a5735fb590fea4b0e35`](https://github.com/randogelist/snditeration/tree/3b184ba109f065d973957a5735fb590fea4b0e35), 26 October 2026.
- [Exact-source CI run 40288194429](https://github.com/randogelist/snditeration/actions/runs/40288194429), [job 121456771906](https://github.com/randogelist/snditeration/actions/runs/40288194429/job/121456771906): successful build, axiom audit and source-placeholder check. The full log reports **8,806 build jobs**, **1,317 theorem declarations checked by the allowlist**, and **312 printed axiom reports**. These are not manuscript-item counts. Inspected axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
- This README update is a source/evidence audit; it does not execute Lean or change the proof mode or execution target. Existing GitHub CI evidence remains separate from native Windows receipts.
- The original publication snapshot contained **`main` and 36 isolated experimental branches**. The new dual-chain publication adds **36 PROP/ALT pairs**, retaining those originals; see the [experiment index](docs/EXPERIMENTS.md#dual-chain-pairs). No new certified paper proof is added. Merged branches, archive families and companion repositories remain separate provenance sources.
- The supplied PDF SHA-256 is `935767c0cda7468f376cd8eadc374077caf6c8a060351d3bea26ac3f838a9d0c`. Numbering was checked against the PDF and `provenance/original_manuscript_Zetahyperbolic.tex` in the supplied `ZETAHYPERBOLIC_10_STAGE_STITCH_v0_1_26_GOODWORKFLOWFRONTIER_TARGETED_COMMUTATIVITY_FIX.zip`.

The register below supersedes stale **status summaries**, not historical proof
receipts. In particular, the older ledger's missing 2.3 `RatFunc.eval` bridge,
unfinished corrected 3.2 pencil and 8/45 total are superseded by the current
source/audit evidence. `CHECKPOINT.json` is an earlier PR #14 receipt, not a
complete inventory of the current tree.

## Later branch evidence — 26 October 2026

[PR #39](https://github.com/randogelist/snditeration/pull/39) is **open and unmerged**. Its source
[`67c962b74112df9f41afe1eb11f69392e7c84cb4`](https://github.com/randogelist/snditeration/tree/67c962b74112df9f41afe1eb11f69392e7c84cb4) passed
[CI 40321257752](https://github.com/randogelist/snditeration/actions/runs/40321257752)
([job 121566462325](https://github.com/randogelist/snditeration/actions/runs/40321257752/job/121566462325)).
The checkout was PR merge commit `fb6483293712b87b06e46be8c521314ddae2ba0f`;
comparison against the recorded source head returned **no changed files**.
Lean 4.33.0 and the pinned Mathlib revision above were inspected.

The full log reports **8,840 build jobs**, **1,888 theorems** and **2,292 project
declarations** in the transitive allowlist audit, with
`AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS`. All **531 printed axiom reports**
use only `propext`, `Classical.choice`, and `Quot.sound`.
The root imports the new modules; recursively inspected imports cover **134 project
modules**, with no missing project source or path to `Experimental`.
These are GitHub CI results on that branch, not Windows receipts or integration into main.

| Item | Newly inspected branch evidence | Boundary |
| --- | --- | --- |
| 3.3 | Actual factorial moment bound and Carleman divergence: [CarlemanDivergence](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/CarlemanDivergence.lean) — component `!!`. | Historical component checkpoint; both remaining clauses are completed by the later continuation receipt above. |
| 3.4 | All-threshold principal eigenvalue-count interlacing and actual arbitrary-order Dodgson identity: [CauchyInterlacing](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/CauchyInterlacing.lean), [PrincipalCondensation](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/PrincipalCondensation.lean) — components `!!`. | Does not repair the false assertion of full finite-root degree at every principal size. |
| 3.6 | [corrected_corollary_3_6](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/CorrectedReciprocalCorollary.lean) — corrected `!!`: rational shifts, log derivatives, exact finite Hankel rank and nearest-root limit. | Corrected finite-family statement only; the original all-order strict positivity and sign/interval errors remain repairs. |
| 3.8 | [PrintedMomentMeasure](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/PrintedMomentMeasure.lean) and [OrthogonalFamilyKernel](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/OrthogonalFamilyKernel.lean) — exact original `!!`: actual measure identification, pole characteristic polynomial for any supplied monic degree-indexed orthogonal family, and its derivative identity for every positive Laplace parameter. | The subsequent exact manuscript comparison is complete; see the correction log. Main has not imported these repairs. |
| 5.2(2) | [theorem_5_2_l2_krein](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section5/KreinL2.lean) — component `!!`: actual integral and convergent signed-channel expansion for arbitrary real L² functions; representative independence is proved. | Does not prove the fixed-K cone assertion in 5.2(3), or the whole printed 5.2. |
| 6.9 | [printed_leading_formula_fails](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section6/TriplePoleCancellation.lean) — refutation component `!!`: at n=1, k=0 the actual scaled limit is 0 whereas the proposed coefficient is 1. | Refutes that coefficient formula only; remaining valuation conclusions need corrected inputs. |

**Main remains at 9/45 exact original statements**, with corrected 3.2 separate.
The new branch results do not certify any experimental scaffold or discharge its
named assumptions automatically. The 108 published experimental heads were
re-read and all match their immutable receipts; there are now **110 live branches**
including main and the PR #39 repair branch. The 72 registered paired attempts
remain unchanged.

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

| Chapter | Contents | Numbered proof items | Whole originals integrated in main | Whole originals verified on PR39 |
| --- | --- | ---: | ---: | ---: |
| 1 | Introduction | 0 | — | — |
| [2](#chapter-2--algebraic-structure-and-canonical-basis-invariance) | Algebraic structure and canonical basis invariance | 4 | 4 | 4 |
| [3](#chapter-3--hyperbolicity-total-positivity-and-spectral-structure) | Hyperbolicity, total positivity and spectral structure | 9 | 1 | 3 |
| [4](#chapter-4--diophantine-approximation-heights-and-root-collapse) | Diophantine approximation, heights and ζ(5) root collapse | 8 | 2 | 2 |
| [5](#chapter-5--weight-seven-integrals-dual-pencils-and-double-poles) | Weight-seven integrals, dual pencils and double poles | 6 | 2 | 3 |
| [6](#chapter-6--structural-barriers-multiweight-couplings-and-further-results) | Structural barriers, multiweight couplings and further results | 18 | 0 | 1 |
| 7 | Discussion and open problems | 0 | — | — |
| **Total** | **35 theorems + 2 lemmas + 5 propositions + 3 corollaries** | **45** | **9** | **13** |

Corrected 3.2 and 3.6 remain separate from both original-statement columns.

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
| Proposition **3.2** · p.8 | Continuous hyperbolic pencil for all real $s > 1$ | **REPAIR; corrected `!!`** | Corrected real-s>1 positive Gram, nonsingular slope, exact degree, real roots and odd-s coincidence. Prefactor corrected to 2(2pi)^(s-1)/Gamma(s); literal paper prefactor is pi/2 times this. ContinuousParameter candidate not imported. **Later verified branch:** Additional actual-family continuity verified on PR39. | [ContinuousPencil](Zetahyperbolic/Section3/ContinuousPencil.lean); [ContinuousDensity](Zetahyperbolic/Section3/ContinuousDensity.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-02_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-02_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/ContinuousFamily.lean) |
| Theorem **3.3** · p.8 | Total positivity, leading sign, and universal signature | OPEN in main; **exact `!!` on PR39** | Whole original verified on PR39: actual printed-measure determinacy, arbitrary all-order mixed minors, exact coefficient-at-degree sign, inertia and primitive root multiplicities. Main retains its historical components only. | [PrincipalPencils](Zetahyperbolic/Section3/PrincipalPencils.lean); [PoleSigns](Zetahyperbolic/Section3/PoleSigns.lean); [SpectralInertia](Zetahyperbolic/Section3/SpectralInertia.lean); [companion criterion](#separate-companion-evidence); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-03_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-03_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/MomentGrowth.lean); [later exact source](https://github.com/randogelist/snditeration/blob/cf32aeef35b5f7cb02b042f672ac9b519c56b25d/Zetahyperbolic/Section3/Theorem33.lean) |
| Theorem **3.4** · p.9 | Root interlacing and Dodgson condensation for principal minors | REPAIR; component `!!` | Principal-root reality, abstract signature restriction, and arbitrary-order polynomial block Dodgson identity proved. Actual constant first principal pencil refutes assuming r finite roots at each size. CauchyInterlacing, PrincipalRadius and actual PrincipalCondensation candidate not imported, so full interlacing/actual Dodgson endpoint remain open in active main graph. **Later verified branch:** PR39 verifies actual eigenvalue-count interlacing, actual condensation and radius monotonicity with their stated singularity conditions. | [PrincipalPencils](Zetahyperbolic/Section3/PrincipalPencils.lean); [SignatureRestriction](Zetahyperbolic/Section3/SignatureRestriction.lean); [DodgsonCondensation](Zetahyperbolic/Section3/DodgsonCondensation.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-04_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-04_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/PrincipalCondensation.lean) |
| Corollary **3.5** · p.10 | Stieltjes J-fraction from interlacing roots | REPAIR; component `!!` | Actual admissible rank-one counterexample refutes literal continued fraction. General normalized Lanczos/no-breakdown and spectral-edge decay still open. | [ContinuedFractionCounterexample](Zetahyperbolic/Section3/ContinuedFractionCounterexample.lean); [ContinuedFractionObstruction](Zetahyperbolic/Section3/ContinuedFractionObstruction.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-05_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-05_alt_construction) |
| Corollary **3.6** · p.11 | Stieltjes reciprocal-root power sums | REPAIR; component `!!` in main; **corrected `!!` on PR39** | Corrected even-moment estimator bounds and convergence at actual spectral center. All-order strict finite-atom Hankel positivity refuted; odd-m sign needs repair. Arbitrary rational-shift/log-derivative and full finite-rank corrected clauses not supplied by local estimator endpoints alone. **Later verified branch:** Complete corrected actual-primitive-polynomial theorem and finite Stieltjes measure verified on PR39; false original not completed. | [ReciprocalMoments](Zetahyperbolic/Section3/ReciprocalMoments.lean); [ReciprocalMomentLimit](Zetahyperbolic/Section3/ReciprocalMomentLimit.lean); [ContinuedFractionObstruction](Zetahyperbolic/Section3/ContinuedFractionObstruction.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-06_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-06_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/CorrectedReciprocalCorollary.lean) |
| Theorem **3.7** · p.11 | Turán non-negativity and Newton log-concavity | OPEN; component `!!` | All-order actual derivative Turan weak/strict/equality, sharp center ratio, normalized coefficient Newton strict/equality criteria, and strict centered Newton hierarchy proved. Individual nonvanishing of every intermediate centered coefficient remains unproved; generic-distinctness argument invalid. | [NewtonTuran](Zetahyperbolic/Section3/NewtonTuran.lean); [ActualNewtonTuran](Zetahyperbolic/Section3/ActualNewtonTuran.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-07_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-07_alt_construction) |
| Theorem **3.8** · p.12 | Christoffel–Darboux pole representation and Jacobi derivative identity | OPEN in main; **exact `!!` on PR39** | ChristoffelDarboux and LaplaceJacobiIdentity candidates exist but are not imported or covered by current main audit. Do not promote source declarations or historical finite-operator components to full actual CD/Laplace identity. **Later verified branch:** The whole exact original, including the supplied-family quantifier, is verified on PR39; it is not integrated into main. | [ChristoffelDarboux](Zetahyperbolic/Section3/ChristoffelDarboux.lean); [LaplaceJacobiIdentity](Zetahyperbolic/Section3/LaplaceJacobiIdentity.lean); [CONTINUATION_MAIN_MERGE_RESOLUTION_20261026](docs/CONTINUATION_MAIN_MERGE_RESOLUTION_20261026.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-08_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-08_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section3/OrthogonalFamilyKernel.lean) |
| Theorem **3.9** · p.13 | Hyperbolicity for Hurwitz and Dirichlet Hankel determinants | OPEN | Actual Hurwitz/Dirichlet positive measures and pole-moment identifications absent from active graph. Historical companion finite character/Fekete components do not close full statement. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-09_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-09_alt_construction) |

Additional numbered items (outside the 45-proof denominator):

- **Remark 3.10** (p.14) — Non-classicality of the Hankel family. Remark: non-classicality needs precise invariant/exclusion proof; printed Favard root-birth argument is not a standalone obstruction.

## Chapter 4 — Diophantine approximation, heights and root collapse

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **4.1** · p.14 | Spectral irrationality measure criterion | OPEN; component `!!` | Local complex-root comparison, lattice index and rational transfer; effective threshold requires explicit computable onset/rates. Printed existence of effective b₀ from bare eventual bounds is not certified. | [TransferComplete](Zetahyperbolic/Section4/TransferComplete.lean); [EffectiveBudget](Zetahyperbolic/Section4/EffectiveBudget.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-01_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-01_alt_construction) |
| Proposition **4.2** · p.15 | Transfer criterion for algebraic approximations of degree $d \ge 1$ | **A-Tier `!!` — exact**; printed hypotheses retained | Exact lattice, degree, nonzero quadratic decay, complex-root separation and height-limsup assumptions imply the printed bound for all algebraic α with bounded extension degree and large naive height. Actual ζ5 input estimates are separate. No effective B₀ is claimed in the printed proposition. | [AlgebraicHeight](Zetahyperbolic/Section4/AlgebraicHeight.lean) |
| Proposition **4.3** · p.15 | Ultrametric zero-free disk over $\mathbb{Q}_p$ | **A-Tier `!!` — exact** | Exact norm-preserving zero-free disk over ℂ_p for integer Q with Q(ξ)≠0; actual primitive polynomial specialization included. Specific ζ-family center valuation is separate. | [ActualPrimitivePadicDisk](Zetahyperbolic/Section4/ActualPrimitivePadicDisk.lean) |
| Theorem **4.4** · p.16 | Sharpened spectral bound and effective irrationality measure for $\zeta(5)$ | OPEN; component `!!` | Actual primitive polynomial with positive normalization, exact degree, nonzero center and finite identities; explicit multiplier, uniform quadratic decay, spectral cap and exponent 25687 remain open. The supplied PDF states the spectral cap 11.411 and measure exponent 25687. | [PrimitivePolynomial](Zetahyperbolic/Section3/PrimitivePolynomial.lean); [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-04_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-04_alt_construction) |
| Theorem **4.5** · p.18 | Irrationality and effective measure for $b\zeta(5) + a\zeta(3)$ | OPEN; source partial | Finite weight-shift determinant reweighting only; coupled density/Loewner bounds, p-adic cancellation, decay and effective measure open. | [ROUND_AUDIT_2026-10-26_ADDITIONAL_CROSSINGS](docs/ROUND_AUDIT_2026-10-26_ADDITIONAL_CROSSINGS.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-05_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-05_alt_construction) |
| Theorem **4.6** · p.19 | Two-sided determinant bounds and coefficient heights | REPAIR; component `!!` | Finite leading-value/Gram/log conservation only; quadratic asymptotics and heights open. Printed use of upper multiplier-rate bound as a lower bound needs repair. | [PotentialGap](Zetahyperbolic/Section6/PotentialGap.lean); [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-06_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-06_alt_construction) |
| Theorem **4.7** · p.21 | Macroscopic exponential root collapse and root separation | OPEN; source partial | Finite cap+average cluster count and root-distance transport; actual family uniform cap/average and arithmetic separation open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-07_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-07_alt_construction) |
| Proposition **4.8** · p.21 | Rational root exclusion and degree bounds for cluster factors | REPAIR / OPEN; source partial | Factor/root-distance inequalities only; rational-root exclusion and effective degree bounds open. Printed proof reverses lower gap into upper cluster bound. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-08_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-08_alt_construction) |

Additional numbered items (outside the 45-proof denominator):

- **Remark 4.9** (p.22) — Spectral bounds and variational conjecture for $\rho_5^*$. Variational envelopes, sandwich constants and claimed consequences not certified as a whole.
- **Remark 4.10** (p.22) — Lee–Yang phase transition at $\zeta(5)$. Free-energy limit and first-order singularity remain unproved; zero pinching alone does not establish a phase transition.
- **Conjecture 4.11** (p.22) — Variational spectral-rate limit. Existence of normalized spectral-norm limit and equality with variational value unproved.

## Chapter 5 — Weight-seven integrals, dual pencils and double poles

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **5.1** · p.22 | Two-variable Beukers measure for $\zeta(7)$ | **A-Tier `!!` — exact** | Actual positive measurable unit-square density, all diagonal/offdiagonal moment identities and explicit rational offdiagonal witness. | [BeukersOffDiagonal](Zetahyperbolic/Section5/BeukersOffDiagonal.lean); [BeukersDensity](Zetahyperbolic/Section5/BeukersDensity.lean); [BeukersRationalMoments](Zetahyperbolic/Section5/BeukersRationalMoments.lean) |
| Theorem **5.2** · p.23 | Dual hyperbolicity and Krein-space decomposition of the two-variable $\zeta(7)$ pencil | REPAIR; parts(1),(2) and refutation `!!` on PR39 | Exact parts(1),(2) are complete. Actual rational fixed-K cones satisfy 2h≤K+1; permitted K=h=2 refutes part(3). Sufficiently-large-K cones and signed-tail control need new proofs. | [ActualDualSpectrum](Zetahyperbolic/Section5/ActualDualSpectrum.lean); [KreinMonomial](Zetahyperbolic/Section5/KreinMonomial.lean); [KreinPolynomial](Zetahyperbolic/Section5/KreinPolynomial.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-02_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-02_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section5/KreinL2.lean); [later exact source](https://github.com/randogelist/snditeration/blob/cf32aeef35b5f7cb02b042f672ac9b519c56b25d/Zetahyperbolic/Section5/ActualKreinDimensionObstruction.lean) |
| Proposition **5.3** · p.24 | Two-variable Beukers measure and dual pencil for $\beta(4) = L(4, \chi_{-4})$ | OPEN in main; **exact `!!` on PR39** | Whole original verified: literal beta(4) positive density and all fourth-power moments, rational polynomial-family integral pencil, exact coefficient-Gram derivative, degree h and all complex roots real. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-03_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-03_alt_construction); [verified destination source](https://github.com/randogelist/snditeration/blob/0672896955e5dc7f7f9b9a0f5340c59e69f0890b/Zetahyperbolic/Section5/BetaBeukersSpectrum.lean) |
| Theorem **5.4** · p.25 | Cancellation of higher zeta values on even pole pairs | **A-Tier `!!` — exact** | Actual τ on simple even-pole pairs, every j≥1 including j=1, and finite rational linearity. | [EvenPoleCancellation](Zetahyperbolic/Section5/EvenPoleCancellation.lean) |
| Theorem **5.6** · p.26 | Weight-seven prime-sum evaluation and pole-ordered refinement | OPEN; source partial | The companion now proves the exact outer integral and refutes two printed continuity clauses. The inner-tail bound, prime-sum asymptotics and local q-adic gains remain. Destination integration of this new companion component remains open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-06_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-06_alt_construction) |
| Theorem **5.7** · p.28 | Simultaneous double-pole Hankel determinant for $\{1, \zeta(5), \zeta(6)\}$ | OPEN | Actual double-pole decomposition, local determinants/valuations and lower-minor bounds unproved. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-07_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-07_alt_construction) |

Additional numbered items (outside the 45-proof denominator):

- **Remark 5.5** (p.25) — Simple-pole scope restriction. 5.4 covers simple poles only; no higher-order extension is asserted or required here.

## Chapter 6 — Structural barriers, multiweight couplings and further results

| Item · PDF page | Statement | Tier of whole item / verified component | Exact scope and remaining work | Source |
| --- | --- | --- | --- | --- |
| Theorem **6.1** · p.29 | Divided-difference $p$-adic valuation law and intrinsic $p^{-6}$ barrier | **REPAIR; exact (1)–(2), complete corrected (3) `!!` on PR39** | Actual Mellin/Jacobian bridge, harmonic lower bounds and valuation -7; full p-adic local residue, determinant norm p^14 and primitive-vector obstruction verified. Literal nonzero-vector clause is refuted by (p,0). Complete corrected theorem is separate from the original count and main proof integration. | [correction and evidence](docs/THEOREM_6_1_CORRECTIONS.md); [exact source](https://github.com/randogelist/snditeration/blob/e56da14673218911252b92790d5fe713aea66e19/Zetahyperbolic/Section6/Theorem61.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-01_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-01_alt_construction) |
| Theorem **6.2** · p.31 | Simultaneous weight-$(6, 7)$ Beukers functional with zero denominator overhead | OPEN in main; **exact `!!` on PR39** | Whole original verified: actual adjacent/extra-denominator integrals, arbitrary integer polynomial and alpha/beta, exact zeta(6)/zeta(7) identity, printed rational correction and proved 6*d_K^7 integer clearing. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-02_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-02_alt_construction); [verified destination source](https://github.com/randogelist/snditeration/blob/0672896955e5dc7f7f9b9a0f5340c59e69f0890b/Zetahyperbolic/Section6/BeukersSimultaneous.lean) |
| Theorem **6.3** · p.32 | Unconditional $q$-adic non-vanishing and explicit positive-cone approximations for $G_{\mathcal{A}}^{(7)}(X)$ | REPAIR; **exact (1) `!!` on PR39** | Part (1) proves the actual q-dimensional paired determinant valuation -7q for every prime q≥5 and every q-integral rational X, with actual Beukers integral identification. Part (2) is refuted by an independently replayed exact h=4 negative direction; that replay is not Lean certification. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-03_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-03_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/Theorem63Nonvanishing.lean) |
| Theorem **6.4** · p.33 | Character–Vandermonde sign cancellation and unconditional hyperbolicity for $\beta(4)$ | REPAIR; **finite pencil/refutation components `!!` on PR39** | Actual odd-square residues, partial fractions, positive slope and full real spectrum are verified for the rational pencil. The printed differential coupling is negative; an explicit corrected positive expression is proved. Actual beta integral calibration remains open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-04_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-04_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/BetaOddPartialFractions.lean) |
| Theorem **6.5** · p.34 | Unconditional $q$-adic non-vanishing for $\Delta_K^{(\beta(4))}(0)$ | OPEN; **actual prerequisite components `!!` on PR39** | Actual integer quotient, odd-prime Euler-moment integrality and weight-4 pole norms are proved. The complete selected-prime Lagrange matrix and determinant valuation remain open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-05_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-05_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/BetaOddPoleNorm.lean) |
| Theorem **6.6** · p.35 | Generalized multi-weight positive-definite pencil | OPEN; source partial | Finite anchored positive cone, full-degree real spectrum and Turán under matrix assumptions; actual multiweight density/arithmetic inputs open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-06_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-06_alt_construction) |
| Theorem **6.7** · p.37 | Universal multi-weight two-variable Beukers Krein decomposition | REPAIR; **exact (1) and cone refutation `!!` on PR39** | Actual multiweight rational pencil has slope CCᵀ, full degree h and all complex roots real for independent rational polynomials. Fixed-K positive/negative h-cones are impossible when 2h>K+1. Infinite Krein convergence and top-weight determinant remain separate. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-07_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-07_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/MultiweightHyperbolicity.lean) |
| Corollary **6.8** · p.38 | Unconditional three-term linear independence cone for $\{1, \zeta(3), \zeta(5)\}$ | OPEN | Three-term linear independence and effective forms inherit unproved 4.5 arithmetic/decay hypotheses. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-08_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-08_alt_construction) |
| Theorem **6.9** · p.38 | Triple-pole and multi-weight Hankel determinants | REPAIR; **uniform refutation/corrected local coefficient `!!` on PR39** | For every n≥1, actual R_n(t)=t³H_n(t) near zero with H_n(0)≠0; H_(n+1)(0)=(n!)⁶. Recompute actual pole rows/congruences before determinant valuation claims. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [verified donor receipt](#separate-companion-evidence); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-09_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-09_alt_construction); [verified PR39 source](https://github.com/randogelist/snditeration/blob/67c962b74112df9f41afe1eb11f69392e7c84cb4/Zetahyperbolic/Section6/TriplePoleCancellation.lean); [later exact source](https://github.com/randogelist/snditeration/blob/cf32aeef35b5f7cb02b042f672ac9b519c56b25d/Zetahyperbolic/Section6/TriplePoleOriginCoefficient.lean) |
| Theorem **6.10** · p.39 | Universal potential-gap identity and vanishing of quadratic derivative growth in two variables | REPAIR; **complete (2) `!!` on PR39** | Exact finite Hadamard bound and zero quadratic log growth are proved for actual independent integer polynomials, all real A≥0 and h=floor(lambda*K), with actual dual-slope identification. Part (1)'s equilibrium limits, strict reweighting and numerical ratio remain open or require repair. | [PotentialGap](Zetahyperbolic/Section6/PotentialGap.lean); [CoefficientGramGrowth](Zetahyperbolic/Section6/CoefficientGramGrowth.lean); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-10_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-10_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/Theorem610CoefficientGrowth.lean) |
| Theorem **6.11** · p.40 | The $p^{-(2k-1)}$ distribution growth law and 2-adic polynomial-quotient obstruction for $\beta(2k)$ | OPEN; source partial | Odd-square scaling/parity only; Euler distribution and odd/2-adic valuation laws open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-11_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-11_alt_construction) |
| Theorem **6.12** · p.42 | Full-dimension sign-flip restoration of positive definiteness and $q$-adic non-vanishing for pure $\beta(4)$ | OPEN | Actual sign-flipped full-dimensional positivity, rational cutoff with spectral margin and q-adic nonvanishing missing. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-12_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-12_alt_construction) |
| Theorem **6.13** · p.43 | Central-factorial secant differential identity, Laplace mode annihilation, and unilateral $(h,0)$ root signature for all $k\ge 1$ | REPAIR; **all-order analytic/Gram components `!!` on PR39** | Actual all-order differential identity, low-mode annihilation, positive exponential envelope, all moments and literal rational-kernel Gram positivity are verified. Printed series needs (-1)^(k-1); infinite-series and beta-functional/slope identification remain open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-13_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-13_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/SecantGram.lean) |
| Theorem **6.14** · p.45 | Even-pole scaling via $\cosh(2\pi v)$ and coupled positive-definite pencils for $b\zeta(5)+a\beta(4)$ and $b\zeta(5)-a\beta(2)$ | REPAIR; **odd-prime unit refutation `!!` on PR39** | The displayed r=1,e=2 moment is -25/256 with v_5=2, refuting the universal valuation-zero assertion. Scaling/Jacobian and functional normalizations still conflict. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-14_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-14_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/BetaScaledUnitObstruction.lean) |
| Theorem **6.15** · p.46 | Arithmetic transcendence, strictly positive one-variable measure, and rank-one Padé pencil for $\beta(2k+1)$ across all $k\ge 0$ | OPEN; **analytic, rational-root/convergence components `!!` on PR39** | Actual all-k positive moments/minors are preserved. The actual pencil now has a unique rational root, correct parity side, exact inverse-Gram error, explicit polynomial error bound and convergence at fixed k,N. Euler/effective arithmetic and the printed stronger asymptotic remain open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-15_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-15_alt_construction); [later exact source](https://github.com/randogelist/snditeration/blob/cf32aeef35b5f7cb02b042f672ac9b519c56b25d/Zetahyperbolic/Section6/BetaOddTotalPositivity.lean); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/BetaOddRootConvergence.lean) |
| Theorem **6.16** · p.47 | Generalized multi-weight Zeta–Beta positive-definite pencil | REPAIR; **refutation and corrected cutoff `!!` on PR39** | Actual H_26^(beta,2) has v_7=-4, refuting the unrestricted -2 bound. The all-order repair 2M≤p^(a+1) ⇒ v_p(H_M^(beta,s))≥-sa is proved. Actual mixed weights and global multiplier conclusions remain open. | [PAPER_GAP_REGISTER](docs/PAPER_GAP_REGISTER.md); [verified donor receipt](#separate-companion-evidence); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-16_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-16_alt_construction); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/Chapter6HarmonicCutoffBound.lean) |
| Theorem **6.17** · p.48 | Universal two-variable Beukers Zeta–Beta pencil, Krein decomposition, and $q$-adic non-vanishing | REPAIR; **fixed-degree/local refutations `!!` on PR39** | Fixed-K positive/negative h-cones require 2h≤K+1; K=h=2 is impossible. Earlier q=11/q=41 proof-step refutations and corrected supports remain verified. Actual multiweight normalization, infinite Krein and full determinant remain open. | [PAPER_GAP_TRACKER](docs/PAPER_GAP_TRACKER.md); [verified donor receipt](#separate-companion-evidence); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-17_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-17_alt_construction); [later exact source](https://github.com/randogelist/snditeration/blob/cf32aeef35b5f7cb02b042f672ac9b519c56b25d/Zetahyperbolic/Section6/BetaHarmonicIndexObstruction.lean); [later chapter proof](https://github.com/randogelist/snditeration/blob/3989d955e6190ab8fabc0720fad136b7e265e074/Zetahyperbolic/Section6/Chapter6ConeDimensionObstruction.lean) |
| Theorem **6.18** · p.49 | Principal-minor 2-adic integrality law, dyadic height bounds for Zeta–Beta pencils, and multi-weight effective measures | OPEN; source partial | Dyadic numerator/denominator degree and quotient-vanishing threshold only; integrality, multiplier, height loss and effective measure open. | [PAPER_GAP_TRACKER](docs/PAPER_GAP_TRACKER.md); [prop](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-18_prop_construction) · [alt](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-18_alt_construction) |

## Separate companion evidence

The companion repository is a source of reusable components, not an automatically
accepted extension of this repository. Its historical `main` snapshot was
[`41674aac3544bf314a53b4302266ad22a30ae707`](https://github.com/randogelist/zetahyperbolic-axiom/tree/41674aac3544bf314a53b4302266ad22a30ae707).
Only README documentation differs from the prior source snapshot
`211b362c16ff6ef73e9a5f2f70c5cbb9a444cf80`, which has [failed CI 40281177876](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40281177876).
Companion [PR #49](https://github.com/randogelist/zetahyperbolic-axiom/pull/49),
earlier source `bdcbb8bbd54d9837e3230cd50c28358eec37ee42`, failed
[CI 40320889232](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40320889232).
The later `b1c99c0d25cf94ee2cfbb398f697b7e50c363f89` run [40326559574](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40326559574) also failed. Subsequent source `7250b47ba4d20ba934e890966a9b77a559689cfd` passed [CI 40327942655](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40327942655): 260 modules, 3,076 theorem declarations and 3,809 declarations, with only the three standard axioms. The [separate companion receipt](docs/receipts/COMPANION_20261026_7250.json) records exact reviewed whole-original 3.8, 5.3 and 6.2 scope. The 5.3/6.2 destination transfers have their own later CI certificate above; donor PASS alone does not supply integration. Additional companion components prove the 5.6 outer integral/continuity refutations, the 6.1 outer off-diagonal valuation and the 6.10 finite sharp Hadamard bound. They do not complete those whole originals or change destination source integration.
The following earlier exact-source receipts were inspected independently; none
closes the corresponding whole paper item or certifies a new destination import.

| Item | Verified component | Exact source and successful run | Open boundary |
| --- | --- | --- | --- |
| 3.3 | `LeanPaper.CarlemanFactorialCriterion.carleman_not_summable_of_factorial_growth` | Unmerged [PR #46](https://github.com/randogelist/zetahyperbolic-axiom/pull/46), source `82fcf7b31da336585fe81bd5b75f0043a69fec4e`; [CI 40279223299](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40279223299) | Generic positive moment sequence with a supplied factorial upper bound; Companion generic criterion only. The later destination continuation independently proves actual determinacy; this donor receipt itself remains component evidence. |
| 6.9 | `Zeta5.HermiteBasisCore.det_coeffMatrix_unimodular'` | Source `ef6cc78ea8ba36f71f38718a3b6af07d4d69217c`; [CI 40270088000](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40270088000) | Prime, distinct-node and congruence inputs; actual triple-pole table/congruence and valuation transfer remain open. |
| 6.16 | `Zeta5Merge.Theorem6_16.weight_comparison_of_compact_ratio` | Source `9814065ae1cba0098f873fea4fc0782dcba23187`; [CI 40262637451](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40262637451) | Positive endpoints and an explicit ratio identity; actual mixed-weight and arithmetic identification remain open. |
| 6.17 | Corrected `harmonic_windows`, `high_unique_multiple`, support and divisibility lemmas | Source `8da5614e6b8994fd163db024c51e3f3512cd1d7f`; [CI 40260089735](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40260089735) | Finite combinatorics only; not the original beta-pencil determinant valuation. |

All four cited companion logs contain an independent visited-set all-project
axiom audit with `AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS` and only
`Quot.sound`, `Classical.choice`, `propext`. Historical success remains attached
to its source and dependencies; it does not turn that failed historical main snapshot into PASS. Later companion main evidence is recorded separately in the Chapter 6 refresh.

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

The earlier arbitrary-L² Beukers–Krein endpoint and original 3.3 are verified on PR39. The [next open original endpoint](docs/NEXT_ENDPOINT.md) distinguishes the false 3.4 clause from actual centered-coefficient nonvanishing in 3.7. Whole 5.2 still needs valid revised cone quantifiers and a signed-tail/subspace proof. Main integration and quantitative arithmetic obligations remain separate.

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
This documentation commit does not trigger a build; the cited source CI is separate. Native Windows
cache/runner receipts remain a separate execution target; no Linux artifact is
silently reused as Windows verification.

Earlier receipts remain under [docs/receipts](docs/receipts/), with exact
[manuscript repair notes](docs/MANUSCRIPT_REPAIRS.md) and
[Section 3 corrections](docs/SECTION3_CORRECTIONS.md). Historical source packets
and proof files are unchanged by this register.

