# Frozen P05.01 target — actual ζ(7) two-variable Beukers moments

Target: Theorem 5.1, equations (5.1) and (5.2), 21 October 2026 manuscript PDF, pp. 22–23.

Exact measure density on (0,1)^2:
  dΩ_7(x,y) = (-log(x*y))^5 / (720*(1-x*y)) dx dy.

Required closure for all r,t in ℕ:
  diagonal r=t: ∫x^r y^r dΩ_7 = ζ(7)-H_r^(7)
  offdiagonal r ≠ t: ∫x^r y^t dΩ_7 = (H_r^(6)-H_t^(6))/(6*(r-t))

Required proof gates: actual positive measurable integrable density, summable geometric expansion, Mellin/Gamma term integrals, series-integral exchange, diagonal and off-diagonal identities and rationality of non-diagonal moments. All Lean sources must be imported into the real main library and audited with #print axioms (only propext, Classical.choice, Quot.sound).

Frozen previous root: b9dfbbfefefb8a0a2e4336a4ff2e2e122f279e2f. Reuses unchanged, already compiled Section5/UnitLogMoments. The completed diagonal and offdiagonal proofs are imported and compiled. The original manuscript integral statement is verified, including positivity and measurability of the density. No ζ(7) irrationality or p-adic cone theorem is claimed.

Workflow: YOU_ARE_GOODWORKFLOWFRONTIER, A_TIER_EXECUTION, P05_01. Reuse mathlib cache and existing PASS-ONCE modules; compile only changed sources. Do not merge a partial theorem as proof of the full printed theorem.

## Final verified receipt — P05_01 A-TIER_LOCAL

- **Single target:** Printed Theorem 5.1, equations (5.1) and (5.2), all r,t≥0.
- **Source proof SHA:** `08d308a22ebe1cc31dfad61b3e875b192290bf17`.
- **PR:** [#24](https://github.com/randogelist/snditeration/pull/24) **MERGED**.
- **Main merge commit:** `1ae34f2bc30135460c357f4efffe1fdbb93d5009`.
- **CI:** [40267850777](https://github.com/randogelist/snditeration/actions/runs/40267850777), **PASS**, 8,783 Lean 4.33 jobs.
- **Axiom audit:** eight targeted proof declarations (log monomial integral, term integral, series interchange, diagonal, offdiagonal, final if-then-else theorem, density positivity and measurability). Every transitive dependency restricted to `propext`, `Classical.choice`, `Quot.sound`.
- **Source scanner:** PASS, zero sorry/admit/custom axiom admissions.
- **PASS-ONCE:** three new Beukers source modules and unchanged Section5/UnitLogMoments retain exact source SHA fingerprints and compiler/toolchain compatibility. The subsequent documentation changes do not recompile any of them.
- **Boundary:** Full *moment integral* proved, not actual two-variable ζ7 *Krein decomposition* (5.2), cones (5.2(3)), or irrationality.

## Final rationality addendum — verified PASS-ONCE

- Statement: `ManuscriptChain.Beukers.offdiagonal_moment_eq_rat` and `offdiagonal_moment_is_rational`.
- Formula: for r≠t, the *actual* two-variable integral is exactly the real cast of `((H_r^(6)-H_t^(6))/(6*(r-t)) : ℚ)`.
- [PR #26](https://github.com/randogelist/snditeration/pull/26) merged with proof SHA `bcb1b496f3e69d97054a6f46c862e00ec967f970`.
- Main merge: `98c11122faa8cfdeb109e4ebba31d1f21d1b505b`.
- [CI run 40268502325](https://github.com/randogelist/snditeration/actions/runs/40268502325): 8,784 Lean 4.33 jobs **PASS**, transitive `#print axioms` for both declarations solely `[propext, Classical.choice, Quot.sound]`, placeholder scan **PASS**.
- No previous Lean proof modules or compatible cached artifacts changed; `Section5/BeukersRationalMoments.lean` is the new independent source.
- **Target P05.01 is completely frozen at the exact paper level.** The next distinct theorem is P05.02(2), which is **not proved by** these integrals.
