# Integration-only — generic ultrametric polynomial disk

Single frozen donor: `snditeration` PR #15, commit `0cee4ea2e32b1f476488f92b476c4eb224285160`; original Git blob `ad1064d1d60b815b29fa458db056f190d19e3508`, source path `Zetahyperbolic/Section4/UltrametricDisk.lean`.

Historical original *individual* module compile: `✔ [8743/8809] Built Zetahyperbolic.Section4.UltrametricDisk`. The bulk PR #15 failed, so this is independent admission only after its own new destination CI.

Exact code provides, for any normed ultrametric field F:
- `norm_eval_le_one`: integer polynomials send closed unit ball into itself;
- `norm_eval_sub_le`: 1-Lipschitz evaluation on the closed unit ball;
- `norm_eval_eq_of_mem_disk`: exact norm preservation on the strict ball centered at x with radius |Q(x)|;
- `eval_ne_zero_of_mem_disk`: corresponding zero exclusion when center value nonzero;
- `padicComplex_zero_free_disk`: specialization to complex p-adic field C_p and center inside unit ball.

These generalize the already proved manuscript Proposition 4.3 as a reusable analytic mechanism. **The complete printed 4.3 was already certified and merged in PR #17.** These five declarations are supporting results, not an additional completed printed item.

Changes isolated to this source file, `Zetahyperbolic.lean` import, five `#print axioms` checks in `Zetahyperbolic/Audit.lean`, and this integration note. Only Mathlib imports used; no edits to the other agent's live 3.3, 3.4, 3.8, 4.2, 5.1, 5.2, 6.9, 6.10 or 6.16 proof branches.

Admission gate: independent GitHub Lean 4.33 build, standard-only transitive axiom reports for all five exact declarations, placeholder scan, verified byte identity, SHA-leased PR merge, and post-merge main CI. All must pass; otherwise leave the draft open for repair.

Compiler target is GitHub CI. No Windows/native Lean receipt is inferred.
