# Noninterfering integration and branch-closure queue

Integration-only mandate: close already-proved isolated modules without changing the other assistant's theorem-development branches. Never treat a draft PR, an individual built module within a failed full PR, or a staged source snapshot as an admitted theorem.

## Verified merged intake

| PR | Outcome | Receipt |
|---|---|---|
| #1–#14 | Historical merged work, preserved and not recompiled needlessly | Previously accepted Lean build/axiom receipts |
| [#17](https://github.com/randogelist/snditeration/pull/17) | Complete printed Proposition 4.3 locally certified | [CI 40259783326](https://github.com/randogelist/snditeration/actions/runs/40259783326) |
| [#18](https://github.com/randogelist/snditeration/pull/18) | Complete printed Lemma 2.3 locally certified by parallel proof agent | [CI 40262441761](https://github.com/randogelist/snditeration/actions/runs/40262441761) |
| [#19](https://github.com/randogelist/snditeration/pull/19) | Independent UnitLogMoments source salvaged and merged, supporting Section 5.1 only | [PR CI 40263400418](https://github.com/randogelist/snditeration/actions/runs/40263400418) and [main CI 40263691978](https://github.com/randogelist/snditeration/actions/runs/40263691978) |

| [snditeration #23](https://github.com/randogelist/snditeration/pull/23) | **INTEGRATED** actual Newton/Turán, merge `9f630aef`; [PR CI 40266691690](https://github.com/randogelist/snditeration/actions/runs/40266691690), [main CI 40266911494](https://github.com/randogelist/snditeration/actions/runs/40266911494) PASS. Whole 3.7 open. |
| [snditeration #25](https://github.com/randogelist/snditeration/pull/25) | **INTEGRATED** six-module finite dual spectrum, merge `484e285e`; [PR CI 40267266192](https://github.com/randogelist/snditeration/actions/runs/40267266192), [main CI 40267527070](https://github.com/randogelist/snditeration/actions/runs/40267527070) PASS. Infinite cones open. |

| [snditeration #27](https://github.com/randogelist/snditeration/pull/27) | **INTEGRATED** conditional complex-root polynomial comparison; merged `c00bb4cf5db3d450449d355a0523a09e68daf351`, [PR CI 40269076009 PASS](https://github.com/randogelist/snditeration/actions/runs/40269076009), [main CI 40269287634 PASS](https://github.com/randogelist/snditeration/actions/runs/40269287634). Does not prove actual ζ5 root gap. |

| [snditeration #30](https://github.com/randogelist/snditeration/pull/30) | **INTEGRATED** — exact conditional printed 4.2 algebraic-number height transfer, 7 original source modules byte-identical, 10 audited declarations. [PR CI 40270563393](https://github.com/randogelist/snditeration/actions/runs/40270563393) and [main CI 40270854695](https://github.com/randogelist/snditeration/actions/runs/40270854695) PASS; merged `7775f7daf2cfb15d7a7614fd30371cc7a1392aed`. **Actual ζ5 rate, separation and height limsup remain hypotheses.** |

## Frozen source donors and protected parallel work

| PR or branch | Restriction |
|---|---|
| [snditeration #22](https://github.com/randogelist/snditeration/pull/22) | **INTEGRATED** as `a4509bc59c465ec484406b86972a08ba395347d5`: corrected real-s density/weighted measure, not full printed 3.2. [PR CI 40265703589](https://github.com/randogelist/snditeration/actions/runs/40265703589) PASS, eight exact standard-only axiom checks. Main [CI 40265897434](https://github.com/randogelist/snditeration/actions/runs/40265897434) also **PASS** after merge. Post-merge all three gates (full Lean, transitive axioms, placeholder scan) passed. |
| [snditeration #24](https://github.com/randogelist/snditeration/pull/24) | **MERGED BY PARALLEL AGENT**, actual full Theorem 5.1 Beukers moments. PR CI 40267850777 PASS, merge `1ae34f2b`; offdiagonal rationality also merged as PR #26, CI 40268502325 PASS. |
| [snditeration #28](https://github.com/randogelist/snditeration/pull/28) | **INTEGRATED** — three exact conditional Section 4.1 transfer modules. PR CI [40269544633](https://github.com/randogelist/snditeration/actions/runs/40269544633) PASS, main CI [40269837877](https://github.com/randogelist/snditeration/actions/runs/40269837877) PASS, 11 standard-only axiom checks. Merge `49379aaaa927b86e238414173aabd8396ab019d7`. Actual-family rate and root-gap inputs remain open. |
| [snditeration #29](https://github.com/randogelist/snditeration/pull/29) | **ACTIVE OTHER AGENT** — actual Theorem 5.2(2) Beukers Krein polarization. Do not modify, merge or close from the integration lane. |
| [snditeration #15](https://github.com/randogelist/snditeration/pull/15) | Frozen failed-CI donor: salvage only independently compiled modules into separate new integration branches, never merge/close bulk PR |
| [snditeration #16](https://github.com/randogelist/snditeration/pull/16) | Inert source-snapshot donor, not compiled in destination; do not merge/close as proof |
| [snditeration #20](https://github.com/randogelist/snditeration/pull/20) | **INTEGRATED** — isolated NewtonTuran (general real-rooted polynomial hierarchy) merged as `8563380bef3f078dee0c29bc39cc9a40d2cf1030`. [PR CI 40265147642](https://github.com/randogelist/snditeration/actions/runs/40265147642) PASS, 7 targeted standard-only axiom reports, placeholder scan PASS. **NOT** the complete printed 3.7 |
| [snditeration #21](https://github.com/randogelist/snditeration/pull/21) | **MERGED BY PARALLEL AGENT**, Theorem 5.4 exact even-pole cancellation; CI 40265986335 PASS. |
| Companion 3.4, 4.2, 5.1, 6.9, 6.10, 6.16 drafts | **ACTIVE OTHER AGENT:** no edits, closures, PR merges or cherry-picks into their branches |

## Noninterference merge gate

1. Create a fresh uniquely named integrate/* branch from the latest main commit. Do not modify donor branches.
2. Port one individually compiled, self-contained theorem module, preserving its source bytes. Require existing Mathlib or accepted destination imports only.
3. Add root import plus exact #print axioms checks and narrow provenance. Open an isolated draft PR.
4. Require the branch's actual full Lean 4.33 build, standard-only axiom audit and proof-placeholder scan PASS. Verify the PR head SHA and mergeability before using an SHA-leased merge.
5. Verify merged source on main and its separate main CI. Then record exact subclaim closure without inflating whole printed theorem counts.
6. Branch deletion is distinct from merge and is not implied. Preserve historical branch refs when they serve as proof evidence.

Current complete printed manuscript count: 9/45 (includes exact printed conditional Proposition 4.2) following the parallel agent’s fully certified Theorem 5.1 (PRs #24 and #26). Generic A-Tier supporting lemmas do not upgrade their whole parent theorem. This queue may be updated only upon a new independently verified merge or an explicit protected-work status change.
