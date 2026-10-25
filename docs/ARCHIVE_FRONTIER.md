# Archive frontier: Section 3

Source inspection, 2026-10-25. This assessment read theorem statements and proof bodies;
it did not compile the archives, establish a new PASS-ONCE, or promote archive receipts.
No complete proof of actual-pencil 3.3(1) total positivity/Carleman, 3.3(3) spectral
signature counts, or full 3.4 interlacing was found in the modules inspected below.

## Exact archive locators

All ZIPs are at the repository root. `A::path` means the exact ZIP entry
`ZETAHYPERBOLIC_CHRONOLOGICAL_LEAN_v1_2_55_KREIN_SIGNATURE_PRINCIPAL_MINORS_FIX1/path`;
the same rule (archive filename without `.zip`, then `/path`) applies to B, C and D.

| Alias | Archive |
| --- | --- |
| A | `ZETAHYPERBOLIC_CHRONOLOGICAL_LEAN_v1_2_55_KREIN_SIGNATURE_PRINCIPAL_MINORS_FIX1.zip` |
| B | `ZETAHYPERBOLIC_PAPER_CHRONOLOGY_v0_6_4_0_CROSS_CHAPTER_FINITE_BRIDGES_433.zip` |
| C | `ZETAHYPERBOLIC_PAPER_CHRONOLOGY_v0_6_0_9_CHRONOLOGICAL_PROOFS_3_2_TO_3_4.zip` |
| D | `ZETAHYPERBOLIC_CHECKPOINT_B_SEQUENTIAL_THEOREMS_v0_4_4.zip` |
| E | `ZETAHYPERBOLIC_PAPER_PROOF_AWARE_PARAGRAPHS_v0_4_8_0 (2).zip` |

E has the internal root `ZETAHYPERBOLIC_PAPER_PROOF_AWARE_PARAGRAPHS_v0_4_8_0/`.

## Reusable actual-pencil ingredients

- **First migration:** B::`Theorem_3_3_Actual_Continuous_Principal_Minors.lean`.
  `PaperChronology.Theorem3_3.ActualContinuousPrincipal.odd_weight_principal_posDef`
  and `odd_weight_all_principal_minors_pos` apply `GRAM_POSITIVE` to an injectively
  chosen submatrix. These prove arbitrary principal minors, not nonprincipal minors.
  Real-s counterparts additionally import the real-s moment-integrability development.
- **Substantial next endpoint:** B::`Theorem_3_4_Actual_Principal_Pencil_Reality.lean`.
  `PaperChronology.Theorem3_4.ActualPrincipal.factorization_without_direction_invertibility`
  constructs the square-root whitening and Hermitian spectral product from positive
  definite base alone; zero spectral parameters are permitted. Its
  `every_complex_root_real_without_direction_invertibility` and
  `odd_all_principal_minors_real_rooted` avoid assuming principal slopes are invertible.
  Dependencies: actual principal-base positivity, CFC square root and Hermitian spectrum.
- B::`Theorem_3_4_Actual_Principal_Spectral_Gap.lean` proves
  `PaperChronology.Theorem3_4.ActualSpectralGap.zero_free_radius_of_posDef` and
  `odd_principal_zero_free`: a positive spectral-budget radius around the center.
  This is local positivity/nonvanishing, not an interlacing theorem.
- B::`Theorem_3_3_Actual_Diagonal_Inertia_Signs.lean` identifies the actual congruent
  diagonal with `poleWeight` and proves its parity sign; the current pole-sign proof
  can supply this ingredient. B::`Theorem_3_3_Actual_Diagonal_Sign_Counts.lean`
  then proves `positiveMass_eq_oddPoleCount`, `negativeMass_eq_evenPoleCount` and
  `weightFive_actual_diagonal_sign_counts` in namespace
  `PaperChronology.Theorem3_3.ActualSignCounts`. These count diagonal entries.
  Missing: a proved Sylvester congruence-to-Hermitian-eigenvalue count transfer.

## Scope boundaries checked against source

- A::`Paper/Theorem_3_3.lean` and A::`Paper/Theorem_3_4.lean` explicitly remain open.
  A::`ProofAdvances/Theorem_3_3.lean` proves actual Gram determinant positivity,
  leading-coefficient product and pole-index sign-set facts. Its 3.4 companion proves
  only the scalar symmetric 3-by-3 Dodgson identity and sign at a minor zero.
- C::`PaperBlueprint/ProofTheorems/Proposition03_02.lean` assumes a family carrying
  base positivity and slope nonsingularity; it is not a real-s analytic construction.
  C::`PaperBlueprint/ProofTheorems/Theorem03_03.lean` gives genuine actual slope
  congruence and spectral-root-side equivalences, not exact inertia counts.
  C::`PaperBlueprint/ProofTheorems/Theorem03_04.lean` closes only 3-by-3 condensation.
- B::`Theorem_3_3_Arbitrary_Order_Gram_Determinant.lean` proves finite square weighted
  Gram determinant algebra under positive weights and invertible evaluation matrix.
  Full continuous nonprincipal total positivity still needs the integral determinant
  identity and generalized Vandermonde signs; Carleman still needs moment growth.
- B::`Theorem_3_4_Reciprocal_Root_Order.lean` proves reciprocal-root monotonicity
  separately on each sign half-line. B::`Theorem_3_4_Shifted_Dodgson_Jacobi.lean`
  proves translated sizes three and four only. Arbitrary-order Jacobi and compatible
  compression/Cauchy interlacing remain separate gaps.
- D::`PaperAudit/Theorem_3_4_Principal_Minor_Counterexample.lean` proves only the exact
  five-residue rational cancellation at `(s,K,N,m)=(5,6,1,1)` by `norm_num`; its
  discussion of an entire family is not a Lean theorem in that file. Allow degree drop.
- E::`PaperChronology/Section3ClosedSignature.lean` proves positivity of signed closed
  residue products and finite energy; E::`PaperChronology/Section3Signature.lean`
  proves finite alternating signed sums. Neither supplies spectral inertia transfer.

Recommended order: migrate actual principal-minor positivity; generalize spectral
factorization to singular slopes and prove actual principal-root reality; then tackle
the Sylvester spectral-count bridge. Keep full 3.3 and 3.4 explicitly unfinished.
