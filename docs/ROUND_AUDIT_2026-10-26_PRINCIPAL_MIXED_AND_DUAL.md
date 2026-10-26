# Exact subclaim sweep — 26 October 2026 (six verification rounds)

## 1. Established GOODWORKFLOWFRONTIER proof tiers

This is an evidence classification, copied faithfully from the user's supplied `YOU_ARE_GOODWORKFLOWFRONTIER_WORKFLOW_DEFINITION_v1_0_15.txt`, **not** a subjective progress scale.

| Marker | Tier | Required proof evidence |
|---|---|---|
| `!` | B-Tier | On-paper mathematical derivation conditional on reasoning; **not** Lean verified |
| `!!` | A-Tier | An exact Lean theorem parsed/elaborated/compiled and transitively axiom audited, without `sorryAx`, hidden axioms or unstated hypotheses |
| `!!!` | Formal closure | The target is reduced by a certified A-Tier implication to finite-witness acceptance by a terminating checker, but no concrete accepted witness yet |
| `!!!!` | S-Tier | Concrete finite raw-data witness **actually accepted** by the terminating checker and the downstream conclusion verified and audited in Lean |

A complete **subclaim** can be A-Tier even though its larger, printed paper theorem is still **OPEN**. Passing source packages in a different repository provide **cross-repo evidence** and do not constitute a new `snditeration/main` receipt.

## 2. Newly crossed exact components in manuscript order

The source snapshot is [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968). All modules below have `status=PASS` with source hash in [`validation/linux/summary.json`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/validation/linux/summary.json). The [219/219-module CI](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869) and [transitive axiom gate](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/validation/linux/proof_integrity.json) passed; allowed logical axioms: `propext`, `Classical.choice`, `Quot.sound`.

| Paper item | A-Tier supporting result crossed off | Exact limitation / next open endpoint |
|---|---|---|
| **3.3(1)** | ✓ ~~Every injectively selected **principal** sub-Gram matrix of the actual odd-zeta positive moment pencil is strictly positive definite at ζ(s), and hence its determinant is positive~~; ✓ ~~every two distinct indices obey the strict 2×2 Gram minor inequality~~. [`ManuscriptChain.PrincipalMinors.gram_posDef`, `determinant_center_pos`, `two_index_strict`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/PaperChain/Stage04PrincipalMinorCenter.lean) | The manuscript asserts **every mixed/nonprincipal minor** det G[I,J]>0. Principal minors, even *all* principal minors, do **not** establish mixed-minor strict total positivity. Still need Andréief+generalized Vandermonde, moment growth and Carleman determinacy. |
| **3.6 corrected rank-sensitive theorem** | ✓ ~~For a finite weighted atomic Hankel measure with **pairwise-distinct nodes** and **strictly positive weights**, the order-n Hankel determinant is positive **iff n≤h**; for n>h it is zero~~. [`weighted_det_pos_iff_order_le_support`, `unweighted_det_pos_iff_order_le_support`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/ProofAdvances/Corollary_3_6_ExactFiniteRank.lean), and [`weighted_hankel_det_zero_above_support`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/ProofAdvances/Corollary_3_6_WeightedCorrected.lean) | This sharpens the **corrected** finite-rank statement; it does not salvage the false printed assertion of strict positivity at *all* orders for a finite-atom measure. Equal/repeated nodes require the number of **distinct** support points rather than h. |
| **3.8(1)** | ✓ ~~The actual symmetric whitened operator `G⁻¹/² M G⁻¹/²` and the signed finite pole operator have **equal characteristic polynomials and equal root multisets**~~. [`LeanPaper.SymmetricPoleSpectrum.actual_symmetric_charpoly_eq_pole`, `actual_symmetric_roots_eq_pole`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/LeanPaper/SymmetricPoleSpectrum.lean) | This includes multiplicity; it is stronger than equality of eigenvalue **sets**. The actual monic orthogonal-polynomial Christoffel–Darboux inverse-Gram kernel is **still not identified** with the spectral pole operator. |
| **5.1–5.2 finite slope** | ✓ ~~For the actual **rational** dual coefficient matrix `C`, the SOS quadratic form vanishes **iff** the coefficient vector belongs to the left nullspace; strict positivity on every nonzero vector is **equivalent to row separation**~~. [`dualSlopeQuadraticForm_zero_iff`, `dualSlopeQuadraticForm_pos_iff_rowsSeparate`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/LeanPaper/ImportedSection56/DualNullspace.lean) | This is the complete **finite coefficient-Gram nullspace test**, not a proof of the 2D Beukers moment integral (5.1) or infinite Krein decomposition (5.2(2)). |
| **5.2(3) finite model only** | ✓ ~~If every negative channel is **identically zero** and the remaining finite positive coefficient rows separate vectors, the finite signed Gram form is positive definite; an analogous statement holds for negative-only channels~~. [`finiteKreinGram_posDef`, `finiteKreinGram_neg_posDef`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/LeanPaper/ImportedSection56/FiniteKreinCone.lean) | These are **finite-channel** tautness-free SOS reductions with strong input assumptions. They do **not** show that a rational polynomial subspace kills the infinite negative Krein tail or satisfy the literal `∀h,K,M` cone statement. The fixed-K dimension obstruction still applies. |
| **6.6 finite matrix cone** | ✓ ~~A finite positive weighted sum of positive-definite real direction matrices yields full-degree real-rootedness, Turán nonnegativity and **strict Turán away from the roots**~~. [`FINITE_MULTIWEIGHT_SPECTRAL_HYPERBOLICITY`, `FINITE_MULTIWEIGHT_STRICT_TURAN`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/LeanPaper/ImportedMultiweight/FiniteMultiweightCone.lean) | `hA`, `hw`, `hdir` are explicit **finite-matrix hypotheses**. The paper's actual **infinite multiweight density** and parameterwise comparison, signature and p-adic valuations are still open. |
| **6.11(2) elementary substitution** | ✓ ~~At the specified odd-square change of variables, `(4w−1)+(2j+1)²=4(w+j(j+1))` and `j(j+1)` is even~~. [`LeanPaper.DyadicQuotientThreshold.odd_square_scaling`, `consecutive_product_even`](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/src/LeanPaper/DyadicQuotientThreshold.lean) | Simple, exact preparatory identities only. They do **not** prove Euler-polynomial p-distribution, dyadic quotient valuations or the full distribution-growth/obstruction theorem. |

**7 new sets of completed exact subclaims** are marked above, across paper items 3.3, 3.6, 3.8, 5.1/5.2, 6.6 and 6.11. Some are refinements of previously broadly described proof work, not seven newly written Lean modules.

## 3. Six rounds — what was actually checked

1. **Active GitHub refs and CI:** `snditeration/main@c521749` and companion `main@86ca99a` remain unchanged. There is **no new full accepted manuscript-item PR**; the broad 51-file `snditeration` PR #15 still has [failed integrated CI](https://github.com/randogelist/snditeration/actions/runs/40188938699).
2. **Uncredited module survey:** enumerated 219 active companion Lean modules and compared its persistent paper ledger with `snditeration`'s 45/64 registers, selecting source-level positive claims not already precisely crossed.
3. **Exact theorem statement inspection:** checked the *types and hypotheses* of selected-index Gram positivity, finite weighted Hankel rank, symmetric pole root multiset, dual row-separation criterion, finite signed Gram and multiweight Turán lemmas.
4. **Independent receipt validation:** each corresponding module appears with a hash and `PASS` status in the companion pinned summary; all 219 modules and the transitive axiom graph passed. No standalone CI/build is falsely asserted for this documentation commit.
5. **Literal manuscript check:** reviewed Theorem 3.3(1), Corollary 3.6, Theorem 5.1/5.2 and Theorem 6.6 against the **52-page PDF supplied with this project**, SHA-256 `935767c0cda7468f376cd8eadc374077caf6c8a060351d3bea26ac3f838a9d0c`; distinguished *principal* from *mixed* minors and *finite* from *infinite* signed measure claims. The PDF is not added to this documentation-only tracker branch.
6. **Historical ZIP source inventory:** enumerated all 25 project ZIP packages and their Lean source counts / top-level status files. The ten-stage and zeta5-spectral packages still have **explicit conditional rate/multiplier premises**, and `ZETA5_NATIVE_WITNESS_SEARCH` explicitly reports `GLOBAL_IRRATIONALITY=NOT_CLAIMED`. No admissible new whole theorem or accepted finite witness emerged from the archives.

## 4. Verified closure accounting

| Status | Count | Meaning |
|---|---:|---|
| **Whole printed items, aggregate exact A-Tier** | **7/45** | `2.2, 2.3, 2.4, 2.5, 3.1, 4.3, 5.4` — **four local**, three companion-only |
| Newly sharpened subclaim groups in this sweep | **7** | Existing audited companion results now individually crossed and properly caveated |
| Remaining incomplete, corrected-only or blocked printed items | **38** | Some include extensive A-Tier subtheorems; none can be relabeled complete without closing its remaining clause |
| `!!!` manuscript-wide finite-witness formal closure | **0** | No such checker reduction has been certified for the full manuscript |
| `!!!!` actual witness admission / S-Tier | **0** | No accepted finite witness / verified transfer for a final RH or full-manuscript goal |

No claim is made here of unconditional ζ(5) irrationality, the `25687` measure, an irrationality proof for ζ(7) from this paper, complete infinite Krein positive/negative subspaces, or any Riemann Hypothesis theorem. Local `snditeration/main` sources remain unchanged; this is **cross-repo verified provenance** only.

See also [the earlier October 26 audit](ROUND_AUDIT_2026-10-26_MOMENTS_AND_POLES.md) and [the machine-readable source-hash ledger](CROSSINGS_MACHINE_2026-10-26.json).
