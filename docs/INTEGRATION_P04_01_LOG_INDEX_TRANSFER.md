# Integration P04.01 — logarithmic index selection and conditional transfer

**Integration-only branch** from `snditeration/main@c00bb4cf5db3d450449d355a0523a09e68daf351`, following accepted PR #27. Frozen PR #15 donor: `0cee4ea2e32b1f476488f92b476c4eb224285160`.

Three source files, each *byte-identical* to its individually compiled donor source:
- `Section4/IndexSelection.lean` — `c2f51ea6474e5bdb033862ea4e920fb1864b9fb5`
- `Section4/TransferComplete.lean` — `3f76567ad096a517deffaa023307392498aaaf8a`
- `Section4/EffectiveBudget.lean` — `498a9ca78bac803b0acc8aecce7fceed05cc4f13`

These modules construct the logarithmic integer lattice `d0 * floor(c log(b)/d0)`, the degree/denominator budget and the rational approximation transfer from assumptions of **quadratic nonzero decay** and **exponential separation from every complex root** of an integer polynomial. The real-exponent/lattice implication assumes the quantitative `hdegree`, `hvalues`, `hroots`. Effective thresholds additionally require an **explicit provided onset**; eventual inequalities alone do not imply computability.

**Not closed by this integration:** actual-family ζ(5) decay, prime multiplier valuations, K-uniform all-root separation, the bound 25687, and manuscript Theorem 4.4. The original paper's effectivity phrase must not be read as proved from unquantified eventual hypotheses.

This isolated integration changes only three source modules, two root imports, eleven audit declarations and this receipt. The other agent's active 3.3, 3.4, 3.8, 4.2, 5.1, 5.2, 6.9, 6.10 and 6.16 branches are untouched.

Merge gate: fresh destination Lean 4.33+frozen Mathlib complete build, standard-only transitive axiom audit of all eleven statements, and placeholder scan PASS. Merge by expected head SHA after checking contemporaneous `main`; confirm post-merge `main` CI. Whole printed theorem count must not increase until its exact complete statement is certified.
