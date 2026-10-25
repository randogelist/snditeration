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

## 2. Manuscript items (45) — tier evidence first

Items follow the original manuscript's order. **A `!!` on a subclaim, corrected result, or conditional transfer does not close the full printed theorem.** Open items receive no unearned B/A/formal/S marker. The seven exact A-Tier items are crossed off; of these, three are verified only in the companion repository.

| # | Paper item | Title | Highest supported tier and scope | Complete printed item? |
|---:|:---|:---|:---|:---|
| 1 | ~~2.2~~ ✓ | Rational functional pullback | `!!` A-Tier, exact **local** | **Complete** |
| 2 | ~~2.3~~ ✓ (cross) | Reflection and difference identities for Tau | `!!` A-Tier, exact **cross-repo** | **Complete** |
| 3 | ~~2.4~~ ✓ | Canonical basis invariance | `!!` A-Tier, exact **local** | **Complete** |
| 4 | ~~2.5~~ ✓ | Lagrange pole diagonalization | `!!` A-Tier, exact **local** | **Complete** |
| 5 | ~~3.1~~ ✓ | Universal hyperbolicity and zero-free disk | `!!` A-Tier, exact **local** | **Complete** |
| 6 | 3.2 | Continuous hyperbolic pencil for all real s > 1 | `!!` A-Tier, **corrected only** | **Corrected only** — printed item requires repair |
| 7 | 3.3 | Total positivity, leading sign, universal signature | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 8 | 3.4 | Root interlacing and Dodgson condensation | `!!` A-Tier, **subclaim**; repair | **Incomplete; repair needed** |
| 9 | 3.5 | Stieltjes J-fraction from interlacing roots | `!!` A-Tier, **subclaim**; repair | **Incomplete; repair needed** |
| 10 | 3.6 | Stieltjes reciprocal-root power sums | `!!` A-Tier, **corrected only** | **Corrected only** — printed item requires repair |
| 11 | 3.7 | Turanian non-negativity and Newton log-concavity | `!!` A-Tier, **subclaim only** | **Incomplete; repair needed** |
| 12 | 3.8 | Christoffel-Darboux pole representation and Jacobi derivative | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 13 | 3.9 | Hurwitz and Dirichlet hyperbolicity | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 14 | 4.1 | Spectral irrationality measure criterion | `!!` A-Tier, **conditional only** | **Conditional only** — original conclusion open |
| 15 | 4.2 | Transfer for algebraic approximations | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 16 | ~~4.3~~ ✓ (cross) | Ultrametric zero-free disk | `!!` A-Tier, exact **cross-repo** | **Complete** |
| 17 | 4.4 | Spectral bound and irrationality measure for zeta(5) | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 18 | 4.5 | Irrationality and measure for b*zeta(5)+a*zeta(3) | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 19 | 4.6 | Determinant bounds and coefficient heights | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 20 | 4.7 | Root collapse and separation | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 21 | 4.8 | Rational root exclusion and cluster degree bounds | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 22 | 5.1 | Two-variable Beukers measure for zeta(7) | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 23 | 5.2 | Dual hyperbolicity and Krein decomposition | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 24 | 5.3 | Beukers measure and dual pencil for beta(4) | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 25 | ~~5.4~~ ✓ (cross) | Higher-zeta cancellation on even pole pairs | `!!` A-Tier, exact **cross-repo** | **Complete** |
| 26 | 5.6 | Weight-seven prime-sum evaluation and pole refinement | — **open / unverified** | **Incomplete** |
| 27 | 5.7 | Double-pole determinant for 1,zeta(5),zeta(6) | — **open / unverified** | **Incomplete** |
| 28 | 6.1 | Divided-difference valuation and intrinsic p^-6 barrier | — **open / unverified** | **Incomplete** |
| 29 | 6.2 | Simultaneous weight-(6,7) Beukers functional | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 30 | 6.3 | q-adic nonvanishing and positive-cone approximations | — original **blocked**; external rational evidence | **Incomplete; repair needed** |
| 31 | 6.4 | Character-Vandermonde sign cancellation and beta hyperbolicity | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 32 | 6.5 | q-adic nonvanishing at zero | — **open / unverified** | **Incomplete** |
| 33 | 6.6 | Generalized multi-weight positive-definite pencil | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 34 | 6.7 | Universal multi-weight Beukers Krein decomposition | — **open / unverified** | **Incomplete** |
| 35 | 6.8 | Three-term linear-independence cone | — **open / unverified** | **Incomplete** |
| 36 | 6.9 | Triple-pole and multi-weight determinants | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 37 | 6.10 | Potential-gap identity and quadratic derivative growth | `!!` A-Tier, **subclaim only** | **Incomplete** |
| 38 | 6.11 | Distribution growth and 2-adic quotient obstruction | — **open / unverified** | **Incomplete** |
| 39 | 6.12 | Full-dimension sign-flip positivity and q-adic nonvanishing | — **open / unverified** | **Incomplete** |
| 40 | 6.13 | Central-factorial secant differential identity | `!!` A-Tier, **subclaim**; repair | **Incomplete; repair needed** |
| 41 | 6.14 | Even-pole cosh scaling and coupled pencils | — **open / unverified** | **Incomplete** |
| 42 | 6.15 | Arithmetic transcendence, positive measure and rank-one law | `!!` A-Tier, **subclaim**; repair | **Incomplete; repair needed** |
| 43 | 6.16 | Generalized multi-weight Zeta-Beta pencil | — **open / unverified** | **Incomplete** |
| 44 | 6.17 | Universal two-variable Zeta-Beta pencil | `!!` A-Tier, **subclaim only** | **Incomplete; repair needed** |
| 45 | 6.18 | Principal-minor 2-adic integrality and dyadic heights | `!!` A-Tier, **subclaim only** | **Incomplete** |

**Current aggregate:** 7 complete printed items out of 45 (**4 local**, **3 companion-only**); **none** at formal closure (`!!!`) or S-Tier (`!!!!`). The [45-item source/evidence table](docs/PAPER_GAP_TRACKER.md), [64 sub-obligation register](docs/PAPER_GAP_REGISTER.md), and [cross-branch resolution audit](docs/CROSS_BRANCH_RESOLUTION_AUDIT_2026-10-25.md) contain precise outstanding assumptions, repairs and compiler receipts.

## 3. Source provenance, outstanding endpoints and maintenance

**Purpose:** a permanent, source-linked inventory of what remains to formalize or repair in the supplied 52-page Zetahyperbolic manuscript. This is documentation, not a second Lean proof implementation. The companion status is *not* automatically imported into `snditeration/main`.

## What is already established in `snditeration`

The pinned [main checkpoint](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/CHECKPOINT.json) reports **846 audited Lean theorem declarations** (including generated declarations), with [passing CI](https://github.com/randogelist/snditeration/actions/runs/40186793090), Lean **4.33.0** and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. It includes substantial *actual-family* mathematics, not merely abstract theorem wrappers:

- Section 2: actual rational-function domains, pullback/reflection, finite-difference algebra, polynomial-basis transport, Lagrange pole diagonalization.
- Section 3: positive hyperbolic moment measure and exact Gram realization; **Theorem 3.1**'s unconditional real roots, primitive degree and sharp operator-norm zero-free disk; spectral inertia/sign parity and root-side counts; principal-root reality; corrected reciprocal-moment estimates and limit.
- Section 4: a proved **conditional arithmetic transfer**, not its actual-family growth/decay assumptions.

See [the frozen local proof ledger](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/docs/FORMALIZATION_LEDGER.md). These 846 declarations must not be mistaken for 846 complete printed results.

## Already crossed off — 7 of 45 complete printed items (aggregate)

The following have exact Lean proofs with passing build/transitive axiom evidence in **at least one** of the two repos:

| Crossed manuscript item | Verification | Remaining work |
|---|---|---|
| ~~Lemma 2.2~~ | **LOCAL PASS** (`snditeration/main`) | None for printed pullback |
| ~~Lemma 2.3~~ | **CROSS-REPO PASS** (`zetahyperbolic-axiom/main`) | Port derivative-at-zero proof into `snditeration`; its stronger local all-RatFunc bridge remains separate |
| ~~Theorem 2.4~~ | **LOCAL PASS** | None for canonical primitive basis invariance |
| ~~Theorem 2.5~~ | **LOCAL PASS** | None for Lagrange pole diagonalization |
| ~~Theorem 3.1~~ | **LOCAL PASS** | None for exact odd-weight hyperbolicity/sharp finite disk; this is **not** a quantitative ζ5 measure |
| ~~Proposition 4.3~~ | **CROSS-REPO PASS** | Port the full `ℂ_p` norm-preserving zero-free disk theorem |
| ~~Theorem 5.4~~ | **CROSS-REPO PASS** | Port actual even-pole cancellation, including `j=1` |

**Aggregate count:** 7/45 complete printed items, comprising **4 certified locally + 3 additional certified in the companion repo**. Only 4 are currently local `snditeration/main` closures; `CROSS-REPO PASS` does **not** mean locally imported or recompiled.

**More work already finished at subclause level:** corrected Proposition 3.2; all-order Dodgson part of Theorem 3.4; corrected Corollary 3.6; strict Newton components of 3.7; effective *conditional* index selection with explicit onset; `CCᵀ` dual-pencil algebra; `6d_K^7` Beukers denominator; finite central-factorial identities; qualitative odd-beta transcendence; polynomial quotient-degree thresholds. **Do not** cross off their full original printed theorems. Full [source-level cross-branch resolution audit](docs/CROSS_BRANCH_RESOLUTION_AUDIT_2026-10-25.md).

## Highest-priority missing pieces

| Priority | Exact unresolved paper endpoint | Concrete closure target |
|:---|:---|:---|
| P1 | **Lemma 2.3** | Prove that the canonical partial-fraction coefficient equals the actual normalized `iteratedDeriv` at 0, with regularity at the origin |
| P2 | **Theorem 3.3(1)** | All mixed Hankel minors strictly positive, plus the Carleman/Stieltjes determinacy proof; the sign/inertia clauses are already locally proved |
| P3 | **Theorem 3.4; Corollaries 3.5–3.6; Theorem 3.7** | Rank-sensitive interlacing, all-order Dodgson, corrected Lanczos fraction, finite-rank moment laws and actual Newton/Turán equality cases |
| P4 | **Theorems 3.8–3.9; Propositions 4.2–4.3; Theorem 5.4** | Actual Christoffel–Darboux/Hurwitz/character identifications and selective, audited reuse of cross-branch results |
| P5 | **Theorems 4.4–4.8** | Real ζ(5) arithmetic multipliers and determinant decay, `‖B_K‖ ≤ exp(11.411 K)`, height/prime estimates, the asserted irrationality exponent **25687** and linear-form transfer |
| P6 | **Sections 5–6** | Actual ζ(7)/β Beukers integrals, infinite Krein/tail bounds, prime sums, double/triple pole valuations, multiweight positivity and arithmetic conclusions |

**Do not try to prove the literally false printed clauses unchanged.** The audit flags: the continuous-density normalization in 3.2; the unnormalized J-fraction in 3.5; all-order strict finite-atomic Hankel positivity / reversed estimate in 3.6; unjustified coefficient-nonvanishing in 3.7; and more serious proposed repairs for 5.6, 6.3, 6.13 and 6.15. The full register separates *proved counterexamples, suspected argument gaps, corrected variants and open theorems*.

## Cross-branch intake is useful, not automatic proof

The independent [Leaned Paper repository](https://github.com/randogelist/zetahyperbolic-axiom) reports a [passing 219-module audit](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) and **7 complete, 21 partial, 10 not formalized, 7 blocked** printed items. Its completed 4.3 and 5.4 and Section 2/3/4 developments are promising selective imports; **none is automatically certified in `snditeration`**. The wide [`feat/zetahyperbolic-continuation-20261025`](https://github.com/randogelist/snditeration/tree/feat/zetahyperbolic-continuation-20261025) supplies many candidate Section 2–6 files but [failed CI](https://github.com/randogelist/snditeration/actions/runs/40188938699) and cannot be credited as A-Tier.

## How this branch stays persistent

Update [the gap ledger](docs/PAPER_GAP_TRACKER.md) after every accepted proof, with **the literal manuscript statement, exact Lean declaration, source commit, compiler/axiom-audit receipt, hypotheses and what remains**. Freeze already proved modules unless their source or dependencies change. Track source integration, compiled lemmas, whole printed theorems and corrected statements separately. Keep historical ZIP archives unchanged.

### Running the underlying Lean project

The active code remains on [`main`](https://github.com/randogelist/snditeration/tree/main). Use the installed Lean 4.33.0 and matching cached Mathlib to run `run.cmd` in the repository root, or `lake build Zetahyperbolic` followed by `lake env lean Zetahyperbolic/Audit.lean`. This documentation-only branch update does **not** claim a new compiler pass.

**Current manuscript completion: OPEN.** No unconditional irrationality of ζ(5) or ζ(7), RH, or S-Tier finite-witness admission is established here.
