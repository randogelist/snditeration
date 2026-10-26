# P06.10 integration-only finite potential and rate-direction certificate

Base: `588230a857acb5a8b74b76ecf99686e79925759c`. Source: frozen donor PR #15 at `0cee4ea2e32b1f476488f92b476c4eb224285160`.
File: `Zetahyperbolic/Section6/PotentialGap.lean`, original Git blob `b855510b32ecadcf5058c7ff8a0237d0cf02f766`, unchanged.
Donor CI `40188938699` reported this individual module built successfully, though the aggregate PR failed elsewhere.

The source formalizes actual finite spectral leading-coefficient/determinant logarithmic identities, rate conservation under **explicit convergence hypotheses**, and a **real-rational counterexample** to inferring `height/epsilon>581` from only `epsilon≥1/2500` and `height+epsilon≥2331/10000`. A corrected sufficient implication requires an **upper** epsilon bound.

This does **not** prove existence of the asymptotic logarithmic potential, strict positive gap, K-uniform decay/height constants, any ζ(5) irrationality bound, or complete manuscript Theorem 6.10. Its named counterexample refutes only the specific inadequate implication.

All other agent-owned branches, including 5.2 actual infinite Krein, companion 3.3/3.4/3.8/6.9, are untouched. Only import/Audit and this file are added. Merge after a new destination pinned Lean 4.33 full build, eleven transitive-axiom checks, placeholder scanner PASS, source Git byte identity and SHA-leased PR merge.