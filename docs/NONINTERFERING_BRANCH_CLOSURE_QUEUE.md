# Noninterfering integration and branch-closure queue

Integration-only mandate: close already-proved isolated modules without changing the other assistant's theorem-development branches. Never treat a draft PR, an individual built module within a failed full PR, or a staged source snapshot as an admitted theorem.

## Verified merged intake

| PR | Outcome | Receipt |
|---|---|---|
| #1–#14 | Historical merged work, preserved and not recompiled needlessly | Previously accepted Lean build/axiom receipts |
| [#17](https://github.com/randogelist/snditeration/pull/17) | Complete printed Proposition 4.3 locally certified | [CI 40259783326](https://github.com/randogelist/snditeration/actions/runs/40259783326) |
| [#18](https://github.com/randogelist/snditeration/pull/18) | Complete printed Lemma 2.3 locally certified by parallel proof agent | [CI 40262441761](https://github.com/randogelist/snditeration/actions/runs/40262441761) |
| [#19](https://github.com/randogelist/snditeration/pull/19) | Independent UnitLogMoments source salvaged and merged, supporting Section 5.1 only | [PR CI 40263400418](https://github.com/randogelist/snditeration/actions/runs/40263400418) and [main CI 40263691978](https://github.com/randogelist/snditeration/actions/runs/40263691978) |

## Frozen source donors and protected parallel work

| PR or branch | Restriction |
|---|---|
| [snditeration #22](https://github.com/randogelist/snditeration/pull/22) | Integration-only corrected real-weight density/measure subclaim for 3.2; source two individually compiled modules from PR15. Require independent CI [40265703589](https://github.com/randogelist/snditeration/actions/runs/40265703589) and exact axiom gate before merger; whole printed 3.2 remains open |
| [snditeration #15](https://github.com/randogelist/snditeration/pull/15) | Frozen failed-CI donor: salvage only independently compiled modules into separate new integration branches, never merge/close bulk PR |
| [snditeration #16](https://github.com/randogelist/snditeration/pull/16) | Inert source-snapshot donor, not compiled in destination; do not merge/close as proof |
| [snditeration #20](https://github.com/randogelist/snditeration/pull/20) | **INTEGRATED** — isolated NewtonTuran (general real-rooted polynomial hierarchy) merged as `8563380bef3f078dee0c29bc39cc9a40d2cf1030`. [PR CI 40265147642](https://github.com/randogelist/snditeration/actions/runs/40265147642) PASS, 7 targeted standard-only axiom reports, placeholder scan PASS. **NOT** the complete printed 3.7 |
| [snditeration #21](https://github.com/randogelist/snditeration/pull/21) — active Theorem 5.4 | **ACTIVE OTHER AGENT:** no edits, closure, cherry-picks or merges |
| Companion 3.4, 4.2, 5.1, 6.9, 6.10, 6.16 drafts | **ACTIVE OTHER AGENT:** no edits, closures, PR merges or cherry-picks into their branches |

## Noninterference merge gate

1. Create a fresh uniquely named integrate/* branch from the latest main commit. Do not modify donor branches.
2. Port one individually compiled, self-contained theorem module, preserving its source bytes. Require existing Mathlib or accepted destination imports only.
3. Add root import plus exact #print axioms checks and narrow provenance. Open an isolated draft PR.
4. Require the branch's actual full Lean 4.33 build, standard-only axiom audit and proof-placeholder scan PASS. Verify the PR head SHA and mergeability before using an SHA-leased merge.
5. Verify merged source on main and its separate main CI. Then record exact subclaim closure without inflating whole printed theorem counts.
6. Branch deletion is distinct from merge and is not implied. Preserve historical branch refs when they serve as proof evidence.

Current complete printed manuscript count: 7/45. Generic A-Tier supporting lemmas do not upgrade their whole parent theorem. This queue may be updated only upon a new independently verified merge or an explicit protected-work status change.
