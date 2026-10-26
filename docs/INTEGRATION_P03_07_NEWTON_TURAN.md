# Independent integration — real-rooted Turán/Newton core

**Ownership:** integration-only. Other ChatGPT agent owns current active theorem derivations. This branch edits only:
- `Zetahyperbolic/Section3/NewtonTuran.lean` (byte-identical donor source)
- `Zetahyperbolic.lean` (new import)
- `Zetahyperbolic/Audit.lean` (seven exact transitive-axiom reports)
- this receipt.

**Donor:** [failed bulk PR #15](https://github.com/randogelist/snditeration/pull/15), source commit `0cee4ea2e32b1f476488f92b476c4eb224285160`, Git blob `772a0cb5941709d0de5408d4a37b20f7a8de2b8e`. Despite overall PR CI failure, its **individual standalone module** built successfully: `⚠ [8759/8809] Built Zetahyperbolic.Section3.NewtonTuran (11s)`. Warning status is not a failure, but requires fresh integrated compilation and axiom review in this branch.

**Exact scope:** this file imports `Mathlib` alone. It establishes general `P.Splits`-based higher-derivative Turán/Laguerre inequalities and normalized Newton inequalities, strictness under explicitly stated distinct-root hypotheses, and the `consecutive_taylor_nonvanishing` conclusion that at a point where `P.eval x ≠ 0`, successive Taylor coefficients cannot vanish simultaneously. Distinguish `HasDistinctRoots` from pairwise simple roots.

**Excluded conclusions:** This proof core does **not** certify full printed Theorem 3.7, specifically its extra assertion of nonzero **every** centered coefficient. It does not settle mixed principal-minor interlacing, spectral radius, or arithmetic estimates. It does not touch the ongoing 3.4, 4.2, 5.1, 5.4, 6.9, 6.10 or 6.16 derivation branches.

**Merge gate:** Fresh destination pinned Lean 4.33.0/Mathlib integrated `lake build` PASS, `lake env lean Zetahyperbolic/Audit.lean` PASS with seven new standard-axiom-only reports, placeholder scan PASS. Use exact head lease when merging; run main CI after merge and preserve source hash unchanged.

**Proof classification if accepted:** `!!` A-Tier generic polynomial **supporting** the paper's Section 3.7, not a whole-manuscript theorem. Whole-item count stays 7/45.
