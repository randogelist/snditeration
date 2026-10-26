import Zetahyperbolic.Section3.LaplaceJacobiIdentity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The printed measure in Theorem 3.8

The square-map realization is identified here with the manuscript's literal
`D_N(t)^(2m) / D_K(t) * w_s(sqrt t; τ) / (2 * sqrt t)` density.
The change of variables is a measure equality, not an informal coordinate
identification or a finite list of moment equalities.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.PrintedMomentMeasure

open LaplaceWeightDerivative LaplaceMomentDerivative LaplaceGramMeasure

def printedDensity (p : Real.Parameters) (τ t : ℝ) : ℝ :=
  LaplaceDenominator.D_real p.N t ^ (2 * p.m) /
    LaplaceDenominator.D_real p.K t * density p.k τ (Real.sqrt t) /
      (2 * Real.sqrt t)

def printedMeasure (p : Real.Parameters) (τ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (printedDensity p τ t))

/-- The manuscript's closed half-line and the open half-line construction
give exactly the same measure; the endpoint has zero Lebesgue measure. -/
theorem printedMeasure_eq_closed (p : Real.Parameters) (τ : ℝ) :
    printedMeasure p τ = (volume.restrict (Ici 0)).withDensity
      (fun t => ENNReal.ofReal (printedDensity p τ t)) := by
  rw [printedMeasure, restrict_Ioi_eq_restrict_Ici]

theorem measurable_printedDensity (p : Real.Parameters) (τ : ℝ) :
    Measurable (printedDensity p τ) := by
  unfold printedDensity LaplaceDenominator.D_real Real.evalQ
  exact (((by fun_prop : Measurable (fun t : ℝ =>
    (Real.realPolynomial (Real.D p.N)).eval t ^ (2 * p.m) /
      (Real.realPolynomial (Real.D p.K)).eval t)).mul
      ((measurable_density p.k τ).comp Real.measurable_sqrt)).div
      (measurable_const.mul Real.measurable_sqrt))

theorem square_image_Ioi :
    (fun y : ℝ => y ^ 2) '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 < y ^ 2
    exact sq_pos_of_pos hy
  · intro ht
    exact ⟨Real.sqrt t, Real.sqrt_pos.mpr ht, Real.sq_sqrt ht.le⟩

theorem square_injOn_Ioi : InjOn (fun y : ℝ => y ^ 2) (Ioi 0) := by
  intro x hx y hy hxy
  nlinarith

theorem printedDensity_square (p : Real.Parameters) (τ : ℝ) {y : ℝ}
    (hy : 0 < y) :
    printedDensity p τ (y ^ 2) = weightedDensity p τ y / (2 * y) := by
  simp only [printedDensity, Real.sqrt_sq hy.le, weightedDensity, weight]

theorem jacobian_printedDensity (p : Real.Parameters) (τ : ℝ) {y : ℝ}
    (hy : 0 < y) :
    ENNReal.ofReal (|2 * y|) * ENNReal.ofReal (printedDensity p τ (y ^ 2)) =
      ENNReal.ofReal (weightedDensity p τ y) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity : 0 < 2*y),
    printedDensity_square p τ hy]
  congr 1
  field_simp [hy.ne'] <;> ring

/-- The full square-map measure is the printed `t`-density, for every Laplace
parameter. No moment truncation is used in this identification. -/
theorem momentMeasure_eq_printed (p : Real.Parameters) (τ : ℝ) :
    momentMeasure p τ = printedMeasure p τ := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  calc
    (∫⁻ t, g t ∂momentMeasure p τ) =
        ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (weightedDensity p τ y) * g (y^2) := by
      rw [momentMeasure, lintegral_map hg (by fun_prop), weightedMeasure,
        lintegral_withDensity_eq_lintegral_mul _
          (measurable_weightedDensity p τ).ennreal_ofReal (hg.comp (by fun_prop))]
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (printedDensity p τ t) * g t := by
      symm
      calc
        _ = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (|2*y|) *
            (ENNReal.ofReal (printedDensity p τ (y^2)) * g (y^2)) := by
          simpa only [square_image_Ioi] using
            (lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
              (f := fun y : ℝ => y^2) (f' := fun y => 2*y)
              (fun y _ => by
                simpa using ((hasDerivAt_id y).pow 2).hasDerivWithinAt)
              square_injOn_Ioi (fun t => ENNReal.ofReal (printedDensity p τ t) * g t))
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          rw [← mul_assoc, jacobian_printedDensity p τ hy]
    _ = ∫⁻ t, g t ∂printedMeasure p τ := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul _
        (measurable_printedDensity p τ).ennreal_ofReal hg

/-- The concrete, cancelled realization agrees with the Laplace measure at
`τ = 1`; cancellation uses exactly the manuscript admissibility hypotheses. -/
theorem concreteMeasure_eq_laplace_one (p : Real.Parameters) (hp : Real.Admissible p) :
    ConcreteMoment.momentMeasure p = momentMeasure p 1 := by
  unfold ConcreteMoment.momentMeasure momentMeasure
  congr 1
  unfold ConcreteMoment.weightedMeasure weightedMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Hyperbolic.weightedDensity_eq_paper p hp hy]
  simp only [weightedDensity, weight, density_one, LaplaceDenominator.D_real]

/-- Exact measure identification for the original, undeformed Theorem 3.8(1). -/
theorem realizationMeasure_eq_printed (p : Real.Parameters) (hp : Real.Admissible p) :
    (REALIZATION p hp).measure = printedMeasure p 1 := by
  change ConcreteMoment.momentMeasure p = printedMeasure p 1
  rw [concreteMeasure_eq_laplace_one p hp, momentMeasure_eq_printed]

theorem printedDensity_one (p : Real.Parameters) (t : ℝ) :
    printedDensity p 1 t =
      LaplaceDenominator.D_real p.N t ^ (2 * p.m) /
        LaplaceDenominator.D_real p.K t * Hyperbolic.density p.k (Real.sqrt t) /
          (2 * Real.sqrt t) := by
  simp only [printedDensity, density_one]

/-- The actual monic family is orthogonal for the literal printed measure. -/
theorem actualPolynomial_orthogonal_printed (p : Real.Parameters) (hp : Real.Admissible p)
    (i j : Fin p.h) :
    (∫ t, (ChristoffelDarboux.actualPolynomial p hp i).eval t *
      (ChristoffelDarboux.actualPolynomial p hp j).eval t ∂printedMeasure p 1) =
      if i = j then ChristoffelDarboux.squaredNorm (GRAM_POSITIVE p hp) i else 0 := by
  rw [← realizationMeasure_eq_printed p hp]
  exact ChristoffelDarboux.actualPolynomial_orthogonal p hp i j

/-- The actual pole kernel uses norms from the literal manuscript measure. -/
theorem actualKernel_eq_printed_sum (p : Real.Parameters) (hp : Real.Admissible p)
    (t u : ℝ) :
    ChristoffelDarboux.actualKernel p hp t u =
      ∑ i, (ChristoffelDarboux.actualPolynomial p hp i).eval t *
        (ChristoffelDarboux.actualPolynomial p hp i).eval u /
        (∫ x, ((ChristoffelDarboux.actualPolynomial p hp i).eval x)^2
          ∂printedMeasure p 1) := by
  simp only [ChristoffelDarboux.actualKernel, realizationMeasure_eq_printed]

/-- The eigenvalues in the original theorem, including their multiplicities,
are exactly the roots of the actual signed pole-kernel characteristic polynomial. -/
theorem actualPole_roots_eq_eigenvalues (p : Real.Parameters) (hp : Real.Admissible p) :
    (ChristoffelDarboux.actualPoleOperator p hp).charpoly.roots =
      Multiset.map (Spectral.actualEigenvalues (Real.manuscriptPencil p)) Finset.univ.val := by
  rw [← ChristoffelDarboux.actual_whitened_roots_eq_pole p hp]
  simpa [Spectral.actualEigenvalues] using
    (Spectral.whitenedMatrix_isHermitian (Real.manuscriptPencil p)).roots_charpoly_eq_eigenvalues

theorem actualPole_roots_nonzero (p : Real.Parameters) (hp : Real.Admissible p) {β : ℝ}
    (hβ : β ∈ (ChristoffelDarboux.actualPoleOperator p hp).charpoly.roots) : β ≠ 0 := by
  rw [actualPole_roots_eq_eigenvalues p hp] at hβ
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hβ
  exact Spectral.actualEigenvalues_ne_zero (Real.manuscriptPencil p)
    (GRAM_POSITIVE p hp) (General.derivative_nonsingular p) i

/-- The deformed kernel has the same printed integral normalization. -/
theorem laplace_kernel_eq_printed_sum (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) (t u : ℝ) :
    ChristoffelDarboux.kernel (gram_positive p hτ) t u =
      ∑ i, (ChristoffelDarboux.monicPolynomial (gram_positive p hτ) i).eval t *
        (ChristoffelDarboux.monicPolynomial (gram_positive p hτ) i).eval u /
        (∫ x, ((ChristoffelDarboux.monicPolynomial (gram_positive p hτ) i).eval x)^2
          ∂printedMeasure p τ) := by
  rw [← momentMeasure_eq_printed]
  exact LaplaceJacobiIdentity.laplace_kernel_eq_orthogonal_sum p hτ t u

/-- The displayed derivative form of (3.8), with the actual density derivative. -/
theorem laplace_logDet_deriv (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    deriv (fun z => Real.log ((gram p z).det)) τ =
      ∫ y in Ioi (0 : ℝ),
        ChristoffelDarboux.kernel (gram_positive p hτ) (y^2) (y^2) * weight p y *
          deriv (fun z => density p.k z y) τ := by
  rw [(LaplaceJacobiIdentity.laplace_logDet_hasDerivAt p hτ).deriv]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [(density_hasDerivAt p.k hτ hy).deriv]

end ManuscriptChain.PrintedMomentMeasure
