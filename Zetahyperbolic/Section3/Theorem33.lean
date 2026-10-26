import Zetahyperbolic.Section3.ActualMixedMinors
import Zetahyperbolic.Section3.SymmetricSquareRoot
import Zetahyperbolic.Section3.SpectralInertia
import Zetahyperbolic.Section3.PoleSigns
import Zetahyperbolic.Section3.PrimitivePolynomial

/-! Exact assembly of the three clauses of manuscript Theorem 3.3.
The determinacy clause refers to the printed measure, not a surrogate moment
sequence. The minor indices are arbitrary increasing row and column selections.
The growth proof even removes the printed auxiliary condition 2mN ≤ K. -/
noncomputable section
open MeasureTheory SignType
open scoped BigOperators

namespace ManuscriptChain

theorem theorem_3_3_total_positivity_determinacy_signature
    (p : Real.Parameters) (hp : Real.Admissible p) :
    (∀ ν : Measure ℝ, (∀ᵐ t ∂ν, 0 ≤ t) →
      (∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν) →
      (∀ n : ℕ, (∫ t : ℝ, t^n ∂PrintedMomentMeasure.printedMeasure p 1) =
        ∫ t : ℝ, t^n ∂ν) → PrintedMomentMeasure.printedMeasure p 1 = ν) ∧
    (∀ (n : ℕ) (rows cols : Fin n → Fin p.h),
      StrictMono rows → StrictMono cols →
      0 < Matrix.det ((Real.gram p (Real.zeta p.weight)).submatrix rows cols)) ∧
    ({i | 0 < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard =
      (if Even p.N then (p.h + 1) / 2 else p.h / 2) ∧
     {i | Spectral.actualEigenvalues (Real.manuscriptPencil p) i < 0}.ncard =
      (if Even p.N then p.h / 2 else (p.h + 1) / 2)) := by
  refine ⟨?_, ?_, SpectralInertia.actual_inertia_formula p hp⟩
  · intro ν hν iν hm
    exact PrintedMomentMeasure.printed_stieltjes_measure_unique p hp ν hν iν hm
  · intro n rows cols hr hc
    exact GRAM_ARBITRARY_MIXED_MINOR_POSITIVE p hp rows cols hr hc

theorem theorem_3_3_weight_five_leading_sign (n : ℕ) :
    sign (BasisInvariance.primitiveNormalization
      (Real.delta (PoleDiagonalization.weightFiveParameters n))
      (PoleDiagonalization.delta_ne_zero _)).polynomial.leadingCoeff =
      (-1 : SignType) ^ (n * (n - 1) / 2) :=
  BasisInvariance.weightFive_primitive_leadingCoeff_sign n

/-- Positive primitive normalization transports the entire polynomial, not only
its zero set. This identity therefore preserves every root multiplicity. -/
theorem primitivePolynomial_real_identity (p : Real.Parameters) :
    (primitivePolynomial p).map (Int.castRingHom ℝ) =
      Polynomial.C ((primitive p).scale : ℝ) *
        (Real.manuscriptPencil p).detPolynomial := by
  have hi := congrArg (Polynomial.map (Rat.castHom ℝ)) (primitive p).identity
  have hc : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext
    simp
  simpa only [Polynomial.map_map, hc, Polynomial.map_mul, Polynomial.map_C,
    Rat.coe_castHom, Real.manuscriptPencil_detPolynomial, Real.realPolynomial,
    primitivePolynomial] using hi

private theorem spectralFactor_roots (center beta : ℝ) (hb : beta ≠ 0) :
    (Spectral.spectralFactor center beta).roots = {center - beta⁻¹} := by
  have he : Spectral.spectralFactor center beta =
      Polynomial.C beta * Polynomial.X + Polynomial.C (1 - center * beta) := by
    simp only [Spectral.spectralFactor, map_sub, map_one, map_mul]
    ring
  rw [he, Polynomial.roots_C_mul_X_add_C _ hb]
  congr 1
  calc
    -(beta⁻¹ * (1 - center * beta)) = center * (beta⁻¹ * beta) - beta⁻¹ := by ring
    _ = center - beta⁻¹ := by rw [inv_mul_cancel₀ hb, mul_one]

/-- The full multiset of roots of the primitive polynomial is the actual
spectral root list. Repeated eigenvalues remain repeated roots. -/
theorem primitivePolynomial_real_roots (p : Real.Parameters) (hp : Real.Admissible p) :
    ((primitivePolynomial p).map (Int.castRingHom ℝ)).roots =
      (Finset.univ : Finset (Fin p.h)).val.map (fun i =>
        Real.zeta p.weight -
          (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹) := by
  classical
  have hs : ((primitive p).scale : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (primitive p).scale_pos)
  have hpos : (Real.manuscriptPencil p).base.PosDef := GRAM_POSITIVE p hp
  rw [primitivePolynomial_real_identity, Polynomial.roots_C_mul _ hs,
    Spectral.detPolynomial_actual_factorization (Real.manuscriptPencil p) hpos,
    Polynomial.roots_C_mul _ (ne_of_gt hpos.det_pos)]
  have hprod : (∏ i : Fin p.h,
      Spectral.spectralFactor (Real.manuscriptPencil p).center
        (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => Spectral.spectralFactor_ne_zero _ _)
  rw [Polynomial.roots_prod _ _ hprod]
  have hf (i : Fin p.h) := spectralFactor_roots (Real.manuscriptPencil p).center
    (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)
    (Spectral.actualEigenvalues_ne_zero (Real.manuscriptPencil p) hpos
      (General.derivative_nonsingular p) i)
  simp_rw [hf]
  exact Multiset.bind_singleton _

/-- The manuscript names the coefficient at h, rather than an unspecified
leading coefficient. The exact-degree theorem identifies these coefficients. -/
theorem theorem_3_3_weight_five_coefficient_sign (n : ℕ) :
    sign ((primitivePolynomial (PoleDiagonalization.weightFiveParameters n)).coeff
      (27 * n)) = (-1 : SignType) ^ (n * (n - 1) / 2) := by
  have hd : (primitivePolynomial (PoleDiagonalization.weightFiveParameters n)).natDegree =
      27 * n := (primitivePolynomial_natDegree _).trans
        (PoleDiagonalization.weightFiveParameters_dimension n)
  rw [← hd, Polynomial.coeff_natDegree]
  exact theorem_3_3_weight_five_leading_sign n

private theorem card_filter_univ_map {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (P : ℝ → Prop) [DecidablePred P] :
    (((Finset.univ : Finset ι).val.map f).filter P).card = {i | P (f i)}.ncard := by
  classical
  rw [Multiset.filter_map, Multiset.card_map]
  change (Finset.univ.filter (fun i => P (f i))).card = _
  have hs : {i | P (f i)} =
      ((Finset.univ.filter (fun i => P (f i)) : Finset ι) : Set ι) := by
    ext i
    simp
  rw [hs, Set.ncard_coe_finset]

/-- The weight-five root counts are counts in the primitive polynomial's root
multiset, hence include algebraic multiplicity explicitly. -/
theorem theorem_3_3_weight_five_root_multiplicity_counts (n : ℕ) (hn : 0 < n) :
    let P := (primitivePolynomial (PoleDiagonalization.weightFiveParameters n)).map
      (Int.castRingHom ℝ)
    (P.roots.filter (fun x => x < Real.zeta 5)).card = 27 * n / 2 ∧
    (P.roots.filter (fun x => Real.zeta 5 < x)).card = (27 * n + 1) / 2 := by
  classical
  dsimp only
  rw [primitivePolynomial_real_roots _ (SpectralInertia.weightFive_admissible n hn)]
  simp only [card_filter_univ_map]
  exact SpectralInertia.weightFive_root_side_counts n hn

/-- The weight-five clauses, with actual B-eigenvalues, the printed coefficient
index, exact degree, and multiplicity counts of the primitive integer polynomial. -/
theorem theorem_3_3_weight_five (n : ℕ) (hn : 0 < n) :
    let p := PoleDiagonalization.weightFiveParameters n
    let P := (primitivePolynomial p).map (Int.castRingHom ℝ)
    (primitivePolynomial p).natDegree = 27 * n ∧
    sign ((primitivePolynomial p).coeff (27 * n)) =
      (-1 : SignType) ^ (n * (n - 1) / 2) ∧
    {i | 0 < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard = 27 * n / 2 ∧
    {i | Spectral.actualEigenvalues (Real.manuscriptPencil p) i < 0}.ncard =
      (27 * n + 1) / 2 ∧
    (P.roots.filter (fun x => x < Real.zeta 5)).card = 27 * n / 2 ∧
    (P.roots.filter (fun x => Real.zeta 5 < x)).card = (27 * n + 1) / 2 := by
  have hi := SpectralInertia.weightFive_actual_inertia n hn
  have hr := theorem_3_3_weight_five_root_multiplicity_counts n hn
  exact ⟨(primitivePolynomial_natDegree _).trans
    (PoleDiagonalization.weightFiveParameters_dimension n),
    theorem_3_3_weight_five_coefficient_sign n, hi.1, hi.2, hr.1, hr.2⟩

end ManuscriptChain
