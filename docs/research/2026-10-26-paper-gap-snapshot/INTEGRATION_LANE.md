# Integration-only lane — noninterference protocol

## Purpose

This lane **closes existing, independently proved Lean modules and finished pull requests**, not new mathematical derivations. It must not modify the proof branches on which another ChatGPT instance is actively creating or deriving results.

**Source of truth:** passing exact Lean 4.33/Mathlib build and standard-only transitive axiom audit, not a theorem's label or source archive name.

## Protected work — do not edit, close or merge on their behalf

- `snditeration` active development: the forthcoming printed Theorem 5.4 integration and any `feat/zetahyperbolic-p05-04*` branch.
- `snditeration` [PR #15](https://github.com/randogelist/snditeration/pull/15): 51-file source donor, globally failed CI. Do not alter its head or close the PR simply because isolated modules can be salvaged.
- `snditeration` [PR #16](https://github.com/randogelist/snditeration/pull/16): **MERGED AS INERT SOURCE ARCHIVE**, not as proofs. Exact 16 `.lean.txt` snapshots remain research data, with successful source-only [CI 40271038633](https://github.com/randogelist/snditeration/actions/runs/40271038633) and merge `aa57382bfb2132ccfb4282803b5c524f7778c646`. Preserve historical branch for provenance.
- `zetahyperbolic-axiom` active draft PRs #3 (6.16), #4 (4.2), #5 (6.10), and any `feat/gwf-target-*` branch. The other instance owns their derivation and sequencing.

This is a **snapshot of 26 October 2026**, not a permanent inference of who owns future branches. Re-query branch/PR activity before each intake.

## Safe independent work

1. Freeze one **nonoverlapping** target in a uniquely prefixed `integrate/*` branch from the current `snditeration/main` SHA.
2. Prefer an isolated module that already compiled at its immutable source commit. Inspect its *full imports* and fully elaborated exact theorem statement. Never treat a failed global PR as global PASS.
3. Copy source byte-identically if possible; keep changes to the minimum integration files and fresh `#print axioms` entries.
4. Open a **draft** integration PR; require destination GitHub Actions full Lean build, exact axiom reports, placeholder scan and mergeability. Require no conflict with concurrent `main` changes. Merge only with an unchanged expected PR head SHA.
5. Inspect `main` after merging and wait for its own build/axiom receipt. Freeze the new source checksum and report the exact scope. **Do not promote a supporting lemma to a complete printed theorem.**
6. Update the persistent gap tracker by one bounded change. Stop that intake cycle; choose another independent donor only after checking the active development frontier again.
7. Do **not** delete already merged feature branches or close useful draft PRs as an automatic side effect. Source cleanup is a separate action requiring a dedicated deletion capability and an explicit retention review.

## Completed integration receipts

| Intake | Donor | Verified exact scope | Destination CI and merge |
|---|---|---|---|
| Proposition 4.3 | Companion's already audited p-adic disk chain | Exact original complex p-adic zero-free disk and actual primitive-polynomial specialization | [PR #17](https://github.com/randogelist/snditeration/pull/17), [CI 40259783326](https://github.com/randogelist/snditeration/actions/runs/40259783326), merge `1e7d422c` |
| Lemma 2.3 | Proven derivative interfaces / destination bridge | Normalized analytic derivative of actual rational pole span and canonical coordinates | [PR #18](https://github.com/randogelist/snditeration/pull/18), [CI 40262441761](https://github.com/randogelist/snditeration/actions/runs/40262441761), merge `c935c996` — completed by the parallel proof agent, **not** this integration lane |
| Section 5.1 Mellin prerequisite | Successful standalone module from failed PR #15 (`0cee4ea2`) | `UnitLogMoments.integral_pow_log`, integrability and exponential substitution for all naturals `a,m`; **not** the Beukers double integral | [PR #19](https://github.com/randogelist/snditeration/pull/19), [PR CI 40263400418](https://github.com/randogelist/snditeration/actions/runs/40263400418), [main CI 40263691978](https://github.com/randogelist/snditeration/actions/runs/40263691978), merge `1c7f2f981097d01620df53b82559dd3352c97bd0` |

## Next opportunities — not yet admitted

Self-contained donor modules inside failed PR #15 may be split into independent `integrate/*` branches. For example `Section5/DualMoments.lean` had a successful module-level build, but it is primarily definitions, so prioritize actual theorem-bearing, nonconflicting sources. `MomentGrowth.lean` depends on `ShiftedMomentPositivity.lean`, which failed in the global PR; it is **not** a standalone safe cherry-pick. Avoid competition with the other instance's 5.4, 4.2, 6.10 and 6.16 targets.

**Proof status:** one additional locally verified analytic supporting lemma from PR #19, no additional *complete printed* manuscript theorem. The original complete-item count remains 7/45.
