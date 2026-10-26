# Cross-project intake for Zetahyperbolic — source snapshots only

Workflow: YOU_ARE_GOODWORKFLOWFRONTIER; intended compiler Lean 4.33.0 with pinned Mathlib.

These 16 byte-preserved companion source snapshots are deliberately stored as .lean.txt data. They are NOT imported by the main Lean library. GitHub CI green on this branch would only certify the unchanged project, not these theorem sources.

Companion provenance: randogelist/zetahyperbolic-axiom at commit 86ca99a23d65cde4880a9005a49076c43e7bc968 (CI PASS 40188664869, standard-only axiom audit). Exact SHA-256 per module in MANIFEST.json.

## Archive admission status (26 October 2026)

This PR closes research-source intake only. It changes no executable Lean imports, does not rebuild the sixteen .lean.txt files, and awards no new A-Tier theorem.

Since the original snapshot, separately compiled destination PRs have already merged for printed 4.3 (PR #17), 2.3 (PR #18), 5.4 (PR #21), finite 5.2(1) (PR #25), and additional independent analytic/Section 4 supports (PRs #19, #20, #22, #23, #27, #28). Their own destination CI receipts establish their status; the staged copies below remain historical provenance.

This source archive remains under research/cross_project_intake and is not an active proof branch. The failed PR #15 and parallel active theorem-development branches are untouched.
## Proposed admission waves

| Wave | Manuscript gaps | Candidate imported theorem | Extra work before merger |
|---|---|---|---|
| P0-C | 4.3 | Complex p-adic norm-preserving zero-free disk, three modules | Independent adapter plus destination compiler and axiom audit; no specific prime valuation claim |
| P0-A | 2.3 | Actual finite pole-span normalized analytic derivative | Complete rational-domain dependency closure; compare Tau functional types |
| P0-B | 5.4 | Even-pole pair cancellation incl. j=1 | Reuse the same Section 2 domain bridge; exact normalization |
| P1-A | 5.1 / 6.2 | UnitLogMoments.integral_pow_log and integrability | New double-integral Fubini, geometric expansion and exact 720 normalization |
| P1-B | 5.2(1–2) | Dual finite roots, coefficient nullspace, algebraic Krein polarization | Actual double Beukers moment identity and infinite summable Krein tails remain open |
| P1-C | 4.1 / 4.7 | All-complex-root comparison and actual spectral root proximity | Uniform root cap and decay in real manuscript K=30n family remain open |
| P1-D | 3.7 | Actual centered Taylor no-two-consecutive-zeros | Every centered coefficient nonzero is NOT proved |
| P2 | 4.8 | ZETA5_NATIVE_WITNESS_SEARCH finite examples | External R2 family mismatches paper; independent Lean interval replay needed |
| P2 | 5.1 / 5.6 / 6.2 | ZETA3, GP7, CHEBYSHEV, IMPACTG sources from ZIP intake | Analytic kernel/object mapping and original-family proofs must be constructed |
| QUARANTINE | 4.4 / 5.6 | zeta5-spectral upstream p-adic, prime and energy methods | Upstream Lean4.34, extra axiom, different family; NOT admissible |

## Admission gate

Import into separate small feature PRs, never overwrite PASS-ONCE frozen modules. Resolve full transitive imports and exact objects; make real source .lean, compile and run print axioms. Check exact manuscript statement and standard-only axioms. Only then merge into main and update persistent gap ledger. No theorem compilation performed for this staging draft.

## Additional user source packet

ZETAHYPERBOLIC_CROSS_PROJECT_INTAKE_v0_1_2.zip (SHA-256 3982d2f1726ccfbae86f3bdcf436f1f8b3ee998bb9f450f20e629dd3c9cef118) collects 30 inert source/data entries from 25 uploaded ZIPs with provenance, quarantine of extra axiom, and finite ζ5 examples. This archive is provided separately in the conversation; its bytes are not committed here.

Earlier snditeration PR #15 is CI FAILED at 0cee4ea2; selectively cherry-pick only after isolated compilation/audit. The goal is to import reliable proofs and then build missing mathematics, not to confuse a source snapshot with a theorem.

## Integrity receipt (26 October 2026)

- Source-to-staging exact Git blob identity: **16/16** staged `.lean.txt` files match their upstream pinned `.lean` blobs byte-for-byte (all comparisons re-read from GitHub).
- PR #16 source-only CI **PASS**: [Actions run 40258829315](https://github.com/randogelist/snditeration/actions/runs/40258829315). This checks **the unchanged imported project**, NOT the 16 source snapshots; no new Lean theorem is admitted by that run.
- User-ZIP source packet: `ZETAHYPERBOLIC_CROSS_PROJECT_INTAKE_v0_1_2.zip`, original 25 source ZIP SHA-256 inventory; all **30** inside-file byte hashes were rechecked and the archive passed its ZIP CRC check.
- User ZIP source dedup: **810 `.lean` archive occurrences; 541 distinct SHA-256 content variants; 269 byte-identical repeats**. Reusing source once is sufficient; repeated archive copies are not independent theorem receipts.
