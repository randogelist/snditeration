# P05.02(2) actual Krein decomposition — frozen proof scope

The exact monomial-moment version of the printed ζ7 Beukers signed Krein decomposition is constructed and axiom-audited in `Zetahyperbolic/Section5/KreinMonomial.lean`. Its finite 6-mode vs 3-mode pairing uses the true Mellin factorials and 1/1440 normalization. No infinite-mode summability is assumed to identify actual monomial moments: the original Theorem 5.1 integral series supplies its own convergence proof.

Open: bilinearity for all rational/real polynomials and extension to arbitrary f∈L²(0,1) with joint continuity and uniform mode control. Do not mark full original Theorem 5.2(2) proved until those are closed.

This is an isolated single-target feature PR. Do not modify the other parallel PR sources. Merging a proved monomial component is permissible only as an explicitly marked subclaim.
