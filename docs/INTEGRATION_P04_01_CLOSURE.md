# Local admission — Section 4.1 generic complex-root and index transfer

**Source donor:** frozen PR #15 at `0cee4ea2e32b1f476488f92b476c4eb224285160`. All five Lean modules were copied byte-identically and compiled in the destination, preserving the original proof bodies.

**Integration #27:** `ComparisonRadius.lean`, `ComplexComparison.lean`; [CI 40269076009 PASS](https://github.com/randogelist/snditeration/actions/runs/40269076009), merged `c00bb4cf5db3d450449d355a0523a09e68daf351`. Post-merge [main CI 40269287634 PASS](https://github.com/randogelist/snditeration/actions/runs/40269287634). Three named axiom reports: standard axioms only.

**Integration #28:** `IndexSelection.lean`, `TransferComplete.lean`, `EffectiveBudget.lean`; [CI 40269544633 PASS](https://github.com/randogelist/snditeration/actions/runs/40269544633), merged `49379aaaa927b86e238414173aabd8396ab019d7`. Post-merge [main CI 40269837877 PASS](https://github.com/randogelist/snditeration/actions/runs/40269837877). Eleven targeted axiom reports: standard axioms only.

**Mathematical scope:** the two imports construct factor-two local polynomial comparison when **all complex roots are separated**, a logarithmic lattice index, radius and denominator budgets from rate hypotheses, an abstract conditional rational approximation measure, and explicit thresholds when computable onset data are provided. They do **not** establish the actual ζ5 family complex-root separation, nonzero quadratic decay, arithmetic multiplier, 25687 exponent or complete printed effective theorem from eventuality alone.

**Concurrency:** integrations used their own `integrate/*` branches. Other agent's active 5.2(2), companion 3.3/3.4/3.8/4.2/5.1/5.2/6.9/6.10/6.16 branches and frozen donor PRs #15/#16 were not edited or closed.

**Whole printed count:** unchanged by the two conditional support imports; manuscript item 5.1 was completed separately by the parallel agent, so current combined complete-item inventory is 8/45.
