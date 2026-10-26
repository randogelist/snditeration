import Zetahyperbolic.Section3.LaplaceGramMeasure
import Zetahyperbolic.Section3.MatrixCurveJacobi

/-! Actual Laplace deformation of the manuscript weight.
Adapted from the companion zetahyperbolic-axiom source; no verification
status is inherited. All results are rechecked in the destination project. -/
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter Matrix Polynomial

namespace ManuscriptChain.LaplaceJacobiIdentity

open ManuscriptChain LaplaceWeightDerivative LaplaceMomentDerivative LaplaceGramMeasure
open ChristoffelDarboux

def derivativeMatrix (p : Real.Parameters) (τ : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => momentDerivative p (i.val+j.val) τ

theorem trace_eq_kernel_integral (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    ((gram p τ)⁻¹ * derivativeMatrix p τ).trace =
      ∫ y in Ioi (0 : ℝ),
        kernel (gram_positive p hτ) (y^2) (y^2) * weight p y * densityDerivative p.k τ y := by
  have hi (i j : Fin p.h) : IntegrableOn
      (fun y : ℝ => ((gram p τ)⁻¹) i j *
        (y^(2*(j.val+i.val))*weight p y*densityDerivative p.k τ y)) (Ioi 0) :=
    (integrable_momentDerivative p (j.val+i.val) hτ).const_mul _
  calc
    _ = ∑ i : Fin p.h, ∑ j : Fin p.h,
        ∫ y in Ioi (0 : ℝ), ((gram p τ)⁻¹) i j *
          (y^(2*(j.val+i.val))*weight p y*densityDerivative p.k τ y) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, derivativeMatrix,
        momentDerivative, integral_const_mul]
    _ = ∫ y in Ioi (0 : ℝ), ∑ i : Fin p.h, ∑ j : Fin p.h,
        ((gram p τ)⁻¹) i j *
          (y^(2*(j.val+i.val))*weight p y*densityDerivative p.k τ y) := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hi i j)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [kernel_eq_inverseGram]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.mul_add, pow_add, pow_mul, pow_mul]
      ring

/-- Formula (3.8), for every positive Laplace parameter. -/
theorem laplace_logDet_hasDerivAt (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun z => Real.log ((gram p z).det))
      (∫ y in Ioi (0 : ℝ),
        kernel (gram_positive p hτ) (y^2) (y^2) * weight p y * densityDerivative p.k τ y) τ := by
  rw [← trace_eq_kernel_integral p hτ]
  exact MatrixCurveJacobi.generic_logDet_hasDerivAt
    (fun i j => gram_entry_hasDerivAt p hτ i j)
    (ne_of_gt (gram_positive p hτ).det_pos)

/-- The kernel appearing in (3.8) is the printed sum of monic orthogonal
polynomials divided by their actual integral squared norms. -/
theorem laplace_kernel_eq_orthogonal_sum (p : Real.Parameters) {τ : ℝ}
    (hτ : 0 < τ) (t u : ℝ) :
    kernel (gram_positive p hτ) t u =
      ∑ i, (monicPolynomial (gram_positive p hτ) i).eval t *
        (monicPolynomial (gram_positive p hτ) i).eval u /
        (∫ x, ((monicPolynomial (gram_positive p hτ) i).eval x)^2
          ∂momentMeasure p τ) := by
  rw [kernel_eq_inverseGram]
  symm
  exact kernel_eq_integral_normalized
    (fun i j => integrable_momentMeasure p (i.val+j.val) hτ)
    (fun i j => (integral_momentMeasure p (i.val+j.val) hτ).symm)
    (gram_positive p hτ) t u


end ManuscriptChain.LaplaceJacobiIdentity
