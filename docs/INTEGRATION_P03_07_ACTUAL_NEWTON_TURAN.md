# Integration-only: actual-family Newton/Turán support for paper §3.7

Donor: `snditeration` failed wide PR #15, immutable source `0cee4ea2e32b1f476488f92b476c4eb224285160`, exact source Git blob `d22f37527ddfacd4b760277a835185a4c4d2097b`. Individual module compiled in that run: `⚠ [8796/8809] Built Zetahyperbolic.Section3.ActualNewtonTuran (6.8s)`, despite other modules failing the aggregate build. Source is ported unchanged.

Dependencies are the already locally verified `NewtonTuran`, `PrimitivePolynomial`, and `SpectralInertia` Lean modules. No external axiom, mathematical premise, or new definition is invented for this integration.

Exact local proof candidates include: actual primitive polynomial splits over real, distinct roots on two sides of zeta center if h≥2, every derivative Turán inequality and strictness, coefficient/shifted/centered Newton inequalities, non-consecutive Taylor coefficient vanishing, strict centered Laguerre, and actual iterated analytic derivative ratio inequalities.

**Not proof of whole manuscript Theorem 3.7:** no assertion every intermediate centered coefficient is individually nonzero; distinct eigenvalues alone do not imply it. No Theorem 3.3 mixed minors or 3.4 interlacing is claimed.

Allowed Lean build: pinned native 4.33.0 + frozen Mathlib. Require fresh GitHub full build PASS, ten exact `#print axioms` reports in `Audit.lean`, standard-only axiom allowlist and placeholder scan PASS. Merge only with expected PR head and verify post-merge main CI. No edits to other agent's 3.3, 3.4, 5.1, 4.2, 6.9, 6.10, 6.16 branches.

Status before CI: source ported/integration in progress, NOT newly certified.