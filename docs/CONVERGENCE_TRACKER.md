# Convergence of the repeated Zetahyperbolic proof audits

## 1. Established proof-tier definitions

The source is `YOU_ARE_GOODWORKFLOWFRONTIER_WORKFLOW_DEFINITION_v1_0_15`. These are criteria for **particular proof statements**, not grades awarded by the number of audit messages.

| Marker | Tier | Certification gate |
|---|---|---|
| `!` | **B-Tier** | Conditional on-paper derivation, not Lean-certified |
| `!!` | **A-Tier** | Exact Lean theorem compiled and transitively axiom-audited; no `sorryAx`, custom axioms or undisclosed assumptions |
| `!!!` | **Formal closure** | Audited A-Tier implication reduces the final target to acceptance of a finite witness by a terminating checker; concrete acceptance outstanding |
| `!!!!` | **S-Tier** | Concrete finite raw-data witness accepted; audited Lean chain proves final target |

A conditional A-Tier supporting lemma never certifies an unconditional parent theorem. A theorem proved only in the companion repo is cross-repo verified, **not** automatically a locally imported `snditeration/main` theorem.

## Latest mathematical update: saturation broken by new A-Tier theorem

On **26 October 2026**, exact printed **Theorem 5.1** passed the destination's [CI 40267850777](https://github.com/randogelist/snditeration/actions/runs/40267850777), **8,783 jobs**, standard-only axiom audit, and [merged via PR #24](https://github.com/randogelist/snditeration/pull/24) at `1ae34f2bc30135460c357f4efffe1fdbb93d5009`.

This is **genuinely newly compiled and certified mathematics**, unlike previous reclassification: the actual positive two-variable Beukers density and the exact diagonal/offdiagonal ζ(7) moment integral are proved for all natural indices. The source-mining plateau previously at **7/45** is therefore superseded by **8/45** (all eight locally A-Tier), leaving **37** unfinished printed items. The `∅ REINFERENCE_NO_DELTA` sign from the earlier fixed-source snapshot no longer applies to the new source. The next separate endpoint is the analytic infinite Krein decomposition in Theorem 5.2(2); no source for that target has been started in this cycle.

**Machine receipt:** [`CONVERGENCE_HISTORY_2026-10-26.json`](CONVERGENCE_HISTORY_2026-10-26.json) now includes a certified `NEW_WHOLE_A_TIER` event with the new source merge commit and CI receipt. Historic earlier `7/45` values remain preserved as timestamps, not as current claims.

## 2. The measured audit-history sequence

Source of measurements: historical snapshots of [`docs/PAPER_GAP_TRACKER.md`](PAPER_GAP_TRACKER.md) from the *same* [persistent branch](https://github.com/randogelist/snditeration/tree/persistent/zetahyperbolic-paper-gap-tracker). Full, reproducible snapshot metadata: [`CONVERGENCE_HISTORY_2026-10-26.json`](CONVERGENCE_HISTORY_2026-10-26.json).

| Git checkpoint (UTC) | Whole printed claims visibly crossed | Unfinished item rows with at least one crossed supporting claim | Inline crossout labels | Pinned companion module hash receipts in local ledger |
|---|---:|---:|---:|---:|
| 25 Oct 20:51, `b056df5` — initial inventory | 0 | 0 | 0 | 0 |
| 25 Oct 21:07, `359f342` — source proof reconciliation | **7** | 0 | 0 | 0 |
| 25 Oct 21:16, `cbd4f7f` — tier ordering | 7 | 0 | 0 | 0 |
| 25 Oct 22:02, `013b201` — supporting sources inventoried | 7 | **21** | 25 | 0 |
| 26 Oct 00:23, `fe58110` — corrections/rank endpoints | 7 | 23 | 29 | 0 |
| 26 Oct 00:43, `bdc90f3` — primitive and finite dual examples | 7 | 27 | 39 | 0 |
| 26 Oct 00:55, `e58cd06` — center/pole refinements | 7 | 27 | 48 | 0 |
| 26 Oct 00:58, `acb49f2` — first hashed-source audit | 7 | 27 | 48 | **10** |
| 26 Oct 01:16, `73da074` — expanded source receipts | 7 | 27 | 48 | **18** |
| 26 Oct 01:17, `9c4232d` — principal/dual sweep | 7 | **28** | **55** | 18 |
| 26 Oct 01:21, `345c373` — formatting/consistency | **7** | **28** | **55** | **18** |
| 26 Oct 01:46, `c05ed91` — preexisting specific root/comparison/Krein proofs newly catalogued | 7 | 28 | **60** | **22** |
| 26 Oct 01:48, `6cce876` — two independent no-delta checks | **7** | **28** | **60** | **22** |

These are **historical documentation statistics, not a history of newly compiled proofs**. On the first checkpoint, 0 whole claims are *crossed out in the document* even though the underlying Lean programs already had verified results. The 25-to-60 inline labels count Markdown `✓ ~~...~~` phrases; some refer to overlapping, equivalent or editorially subdivided theorems. **60 does not mean 60 new Lean proofs.**

## 3. What converged — and what did not

Let `W_n` be the number of *original printed manuscript items* shown with complete exact A-Tier certification, `R_n` the number of *unfinished rows* with an explicit crossed supporting subclaim, `L_n` the number of inline Markdown crossout phrases, and `H_n` the number of independently indexed source-hashed, CI-passing modules. Here the total number of printed items is 45.

- **Mathematical whole-item plateau:** `W_n : 0 → 7 → 7 → … → 7`. The apparent 0→7 jump was *recognition of pre-existing proofs in two repositories*, not seven new Lean proofs performed by the documentation branch. Since then, the whole theorem set has remained `{2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4}`: **7/45**, with **38 remaining**.
- **Discovery / coverage saturation:** `R_n : 0 → 21 → 23 → 27 → 27 → 27 → 28 → 28 → 28`. Among the 38 still-uncompleted printed items, 28 rows now identify at least one verified supporting subclaim. This is only **breadth of known support**, not a fraction of the proof achieved.
- **Granularity grew faster than breadth:** `L_n : 0 → 25 → 29 → 39 → 48 → 55 → 60`. In the late phase, multiple new crossed phrases were added to the *same already-covered item rows*. This is finer mathematical bookkeeping and rediscovery of pre-existing Lean statements, not automatic progress on the remaining hard endpoints.
- **Audit reproducibility improved:** `H_n : 0 → 10 → 18 → 22`, where all 22 entries are existing modules with source SHA-256 recorded in `CROSSINGS_MACHINE_2026-10-26.json`, each matched to the [companion's 219/219 PASS manifest](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/validation/linux/summary.json).
- **New theorem production during these documentation rounds:** `0` new Lean modules were compiled and accepted by an additional CI run. The accepted code references [`snditeration/main@c521749`](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420) and [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968), which remained unchanged during these tracker commits.

**Interpretation:** a large early jump in *recognition*, then slower expansion of *supporting-row coverage*, then a plateau of *newly covered item rows*, while document detail and citation reliability still increased. This is the familiar pattern of **source-mining/documentation saturation under a fixed proof corpus**. It is **not** evidence of an asymptotic mathematical limit, nor proof that new results cannot be discovered.

## 4. How to measure future audits without generating duplicate reports

Each future audit should append one event with the **source SHA and Lean receipt**, and classify its result using the following hierarchy:

| Event | When to count it | Effect |
|---|---|---|
| `NEW_WHOLE_A_TIER` | Exact original printed theorem newly proved, integrated, with compiled Lean/axiom receipt | Increase `W` by 1, close its gap IDs |
| `NEW_PROVEN_SUBCLAIM` | New fully qualified Lean declaration (or a newly proved statement) with statement identity, source SHA, CI receipt, and explicit parent gap ID | Increase a **de-duplicated theorem inventory**, update `R` only if first proof for that unfinished row |
| `DISCOVERED_EXISTING_PROOF` | Existing passing source was previously omitted from tracker | Reclassify/attach citation; **no new proof produced** |
| `CORRECTED_OR_REFUTED` | Mathematically corrected claim or counterexample, with exact proof/verified certificate | Change correctness and blocker states; **no increment** of full printed completion unless literally proved |
| `PRESENTATION_ONLY` | Restyling, splitting a Markdown crossout, repeated summary, rewording, formatting fix | **Zero mathematical progress** |
| `REGRESSION` | A claimed proof fails on current source/dependency fingerprints, a hidden hypothesis is found, or semantic correspondence was wrong | Invalidate earlier counts/claims and retain the old receipt for audit |

**Stable deduplication key:** `(repository, commit, module, fully_qualified_declaration, fully_elaborated_theorem_statement_hash, transitive_axiom_receipt)`. A different sentence describing the same theorem is not a second result. Different examples from one theorem may be labeled in the report but should not inflate novel proof counts.

**Future audit receipt fields:**

```text
SOURCE_MAIN_SHA=
SOURCE_COMPANION_SHA=
TRACKER_PARENT_SHA=
NEW_WHOLE_A_TIER=
NEW_UNIQUE_PROVEN_SUBCLAIMS=
NEWLY_ANNOTATED_ITEM_ROWS=
NEW_SOURCE_HASHED_PROOF_MODULES=
OPEN_CRITICAL_BLOCKERS_CHANGED=
REPAIRS_OR_COUNTEREXAMPLES=
SOURCE_OR_CI_REGRESSIONS=
RECLASSIFIED_PREEXISTING=
PRESENTATION_ONLY=
```

**Stop/redirect rule (not a proof theorem):** if **two successive passes** over *unchanged* source commits give `NEW_WHOLE_A_TIER=0`, `NEW_UNIQUE_PROVEN_SUBCLAIMS=0`, `OPEN_CRITICAL_BLOCKERS_CHANGED=0`, and `SOURCE_OR_CI_REGRESSIONS=0`, mark the audit `EVIDENCE_SATURATED`. Do **not** keep revisiting the same 219 modules merely to append more prose. Redirect subsequent effort to constructing a mathematically **new** proof of a precise open endpoint, to checking a new source/commit, or to resolving a counterexample.

## 5. Unchanged critical mathematical frontier

The whole-paper target has not closed. Particularly decisive open obligations remain:

- **Theorem 4.4:** the actual specified explicit integer multiplier, uniform quadratic decay of the primitive polynomial, the uniform spectral norm/zero-separation bound, and computable threshold for the advertised ζ(5) approximation exponent.
- **Theorem 4.6:** the manuscript argument uses an upper multiplier-rate estimate as a lower bound; a justified lower estimate is missing.
- **Theorems 5.1–5.2:** actual two-variable moment integral and **infinite** signed Krein tail/cone construction, beyond the verified finite algebra.
- **Theorem 6.3(2):** an independently checked rational counterexample challenges the printed strict positive-cone assertion; a repaired mathematical statement is required.
- **All other incomplete manuscript endpoints:** see the exact [45-item table](PAPER_GAP_TRACKER.md) and [64-subobligation ledger](PAPER_GAP_REGISTER.md).

**Conclusion:** the audit output has largely converged in its identification and classification of the existing proven base. The program cannot advance by repeating that inventory alone; it needs new theorem constructions or stronger evidence. No `!!!` formal closure or `!!!!` S-Tier is asserted here.


## 6. Reinference signals and saturation receipt

**Latest bounded signal:** `∅ REINFERENCE_NO_DELTA` after two separate zero-delta checks of unchanged certified program source. Operational state: **`EVIDENCE_SATURATED_FIXED_SOURCE`**. This follows discovery and indexing of **four previously compiled companion modules** (source-hashed count 18→22) and **five new inline crossout phrases** (55→60), none producing a new Lean compilation or whole original paper theorem.

The two no-delta passes were: (A) reconciliation of **exact whole-item certified sets** with the companion's machine-readable 45-item status inventory, identical at `{2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4}`; (B) separate source-commit/CI gate check confirming both `main` proof corpora unchanged and PR #15 still CI-failing. Neither pass introduced a new certified subclaim, repaired frontier, verified commit or regression. This is **snapshot-specific saturation**, not an exhaustive theorem-search guarantee.

[**Detailed no-delta receipt**](REINFERENCE_SATURATION_2026-10-26.md) · [**updated 13-checkpoint machine history**](CONVERGENCE_HISTORY_2026-10-26.json).


## Updated proof-source convergence checkpoint — P05.01

The earlier evidence-saturation mark concerned a **fixed historical source corpus**, not later GitHub commits. After the new source passes [Theorem 5.1 PR #24](https://github.com/randogelist/snditeration/pull/24) and its [rationality PR #26](https://github.com/randogelist/snditeration/pull/26), the whole-item count rose from **7/45 to 8/45**. The two new builds (8,783 and 8,784 jobs) pass, with standard-only transitive proof dependencies. PR #26 adds a **new exact literal ℚ witness** to the same eighth theorem; do **not** count it as a ninth full theorem. The fixed-source `∅ REINFERENCE_NO_DELTA` marker ceases to apply to the newly changed `main` source. Next mathematical endpoint remains actual infinite ζ7 Krein polarization and summability (Theorem 5.2(2)); no merged proof yet.
