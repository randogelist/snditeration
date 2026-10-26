# P05.02(2) actual Krein decomposition — frozen proof scope

The exact monomial-moment version of the printed ζ7 Beukers signed Krein decomposition is constructed and axiom-audited in `Zetahyperbolic/Section5/KreinMonomial.lean`. Its finite 6-mode vs 3-mode pairing uses the true Mellin factorials and 1/1440 normalization. No infinite-mode summability is assumed to identify actual monomial moments: the original Theorem 5.1 integral series supplies its own convergence proof.

Open: bilinearity for all rational/real polynomials and extension to arbitrary f∈L²(0,1) with joint continuity and uniform mode control. Do not mark full original Theorem 5.2(2) proved until those are closed.

This is an isolated single-target feature PR. Do not modify the other parallel PR sources. Merging a proved monomial component is permissible only as an explicitly marked subclaim.

## Locally verified finite checkpoint (FROZEN)

- `P05_02_2_FINITE_KREIN=A_TIER_LOCAL_PARTIAL`
- Proof head: 372deda8edc77bba6312b8f80137e00e1b75e74f
- Merge: 588230a857acb5a8b74b76ecf99686e79925759c
- Full-source CI: https://github.com/randogelist/snditeration/actions/runs/40271072845
- CI outcome: PASS (8,798 jobs, six exact axiom reports, placeholder scanner PASS).
- Axiom allowlist: `propext`, `Classical.choice`, `Quot.sound` exclusively.
- Monomial source Git blob: `9f4e12d26e12e55ad1ab42603d40706eefa88ed7`.
- Polynomial source Git blob: `f420c1fdcd638724c1aa0be1c46957c023d6d172`.
- Actual `L²(0,1)` scope: OPEN; completed theorem is genuinely source-backed only for actual monomials and their finite coefficient bilinear extension.
- This is a theorem subclause, not a completion of original Theorem 5.2(2).
