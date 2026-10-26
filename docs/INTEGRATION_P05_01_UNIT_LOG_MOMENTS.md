# Independently salvage UnitLogMoments from failed PR #15

Integration ownership: this branch only. **Do not modify** PR #15, the separate P05.04 development, or companion work on 4.2, 6.10 and 6.16.

Frozen input: `snditeration@0cee4ea2e32b1f476488f92b476c4eb224285160`,
`Zetahyperbolic/Section5/UnitLogMoments.lean`.
Upstream Git blob: `7523106b16d1da8499619a671d7cb37efb35bbb4`.
Historical PR #15 individual build line:
`✔ [8747/8809] Built Zetahyperbolic.Section5.UnitLogMoments`.
Its **integrated** build failed elsewhere, so no prior complete PR admission is inferred.

Exact subclaim: For natural a,m, the integral on (0,1) of
`u^a * (-Real.log u)^m` equals
`(m.factorial : ℝ) / (a+1)^(m+1)`.
The source also proves its integrability and the change of variables
`u = exp(-x)`.

This is an **analytic support lemma** for manuscript Theorems 5.1 and 6.2;
it does not prove the actual two-variable Beukers integral, Fubini/series
interchange, off-diagonal rational moments, or ζ(7) irrationality.

**Admission gate:** GitHub Lean 4.33 pinned Mathlib full imported-build PASS;
`Zetahyperbolic/Audit.lean` reports standard-only transitive axioms for four
declarations; placeholder scan PASS. Only then merge with SHA lease.
Leave earlier frozen modules untouched.

After merge, record separately as a **locally compiled subclaim** in the
persistent gap tracker, without increasing the original whole-item 7/45 count.
