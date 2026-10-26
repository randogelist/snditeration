# Frozen P05.01 target — actual ζ(7) two-variable Beukers moments

Target: Theorem 5.1, equations (5.1) and (5.2), 21 October 2026 manuscript PDF, pp. 22–23.

Exact measure density on (0,1)^2:
  dΩ_7(x,y) = (-log(x*y))^5 / (720*(1-x*y)) dx dy.

Required closure for all r,t in ℕ:
  diagonal r=t: ∫x^r y^r dΩ_7 = ζ(7)-H_r^(7)
  offdiagonal r ≠ t: ∫x^r y^t dΩ_7 = (H_r^(6)-H_t^(6))/(6*(r-t))

Required proof gates: actual positive measurable integrable density, summable geometric expansion, Mellin/Gamma term integrals, series-integral exchange, diagonal and off-diagonal identities and rationality of non-diagonal moments. All Lean sources must be imported into the real main library and audited with #print axioms (only propext, Classical.choice, Quot.sound).

Frozen previous root: b9dfbbfefefb8a0a2e4336a4ff2e2e122f279e2f. Reuses unchanged, already compiled Section5/UnitLogMoments. The current imported series module is under construction until it passes destination Lean4.33 CI, and full Theorem 5.1 remains open until offdiagonal proof is also completed. No ζ(7) irrationality or p-adic cone theorem is claimed.

Workflow: YOU_ARE_GOODWORKFLOWFRONTIER, A_TIER_EXECUTION, P05_01. Reuse mathlib cache and existing PASS-ONCE modules; compile only changed sources. Do not merge a partial theorem as proof of the full printed theorem.
