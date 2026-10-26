# Independent integration — finite dual spectrum of Theorem 5.2(1)

**Single frozen target:** finite-dimensional rational coefficient-pencil part of the printed Theorem 5.2(1). This is independent of other-agent development of the actual two-variable Beukers integral (Theorem 5.1), the infinite Krein series and polynomial cone problems.

**Source:** failed bulk PR #15 at commit `0cee4ea2e32b1f476488f92b476c4eb224285160`. Six individually compiled modules are copied byte-for-byte: `DualMoments`, `DualAffineAlgebra`, `DualPencilCCT`, `CoefficientGram`, `PositiveSlopeSpectrum`, `ActualDualSpectrum`. Their DAG imports only Mathlib, these six modules, `Section2.Moments` and `Section3.RootFactorization` already on main. The full bulk PR failed elsewhere.

**Mathematical target:** for a rational coefficient-row matrix with independent rows, its slope `CCᵀ` is positive definite; the associated exact rational dual determinant has degree h, factors over real roots, and every complex root is real. All assumptions are explicit. No hypothesis of ζ(7) irrationality or unconditional all-dimensional Krein cone is smuggled in.

**Excluded:** the genuine two-variable Beukers integral identity, geometric series and Fubini, off-diagonal rational moment formula, the infinite signed Krein sum, tail controls, and Theorem 5.2(3). The full original Theorem 5.2 remains open; this builds and certifies its finite spectral subsection only.

**Admission gate:** Lean 4.33.0 with pinned Mathlib must compile the **entire** destination root import, complete `Zetahyperbolic/Audit.lean` with targeted `#print axioms`, and pass the proof-placeholder scanner. A fresh destination CI PASS with standard-only axioms and byte-identity evidence is mandatory; merge only using a SHA lease, then verify main.

**Noninterference:** no changes to the other agent's 3.3, 3.4, 5.1, 4.2, 6.9, 6.10, 6.16 working branches. No edits to frozen PR #15 or research PR #16. This integration belongs solely to `integrate/pr15-finite-dual-spectrum-v1`.
