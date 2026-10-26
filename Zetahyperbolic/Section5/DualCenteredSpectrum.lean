import Zetahyperbolic.Section5.RationalIndependence
import Zetahyperbolic.Section3.ActualSpectrum

/-!
# Theorem 5.2(1): actual centered eigenvalues of the dual pencil

The real factors here are the eigenvalues of the explicitly constructed
M^(-1/2) G(ξ) M^(-1/2), where M=CCᵀ. No chosen spectral certificate is
assumed or substituted for this matrix.
-/
noncomputable section
open Matrix Polynomial
open scoped BigOperators MatrixOrder
namespace ManuscriptChain.DualSpectral

variable {h : ℕ}

/-- Auxiliary symmetric pair used only to invoke the existing square-root API. -/
def whiteningData (p : PositiveSlopePencil h) (ξ : ℝ) : Spectral.SymmetricAffinePencil h where
  center := ξ
  base := p.slope
  direction := p.constant + ξ • p.slope
  base_symmetric := Matrix.isHermitian_iff_isSymm.mp p.slope_posDef.isHermitian
  direction_symmetric := p.constant_symmetric.add
    ((Matrix.isHermitian_iff_isSymm.mp p.slope_posDef.isHermitian).smul ξ)

def centeredDualMatrix (p : PositiveSlopePencil h) (ξ : ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  Spectral.whitenedMatrix (whiteningData p ξ)

def centeredDualEigenvalues (p : PositiveSlopePencil h) (ξ : ℝ) : Fin h → ℝ :=
  Spectral.actualEigenvalues (whiteningData p ξ)

/-- Literal matrix formula in manuscript Theorem 5.2(1), using the symmetric square root. -/
theorem centeredDualMatrix_eq (p : PositiveSlopePencil h) (ξ : ℝ) :
    centeredDualMatrix p ξ =
      (CFC.sqrt p.slope)⁻¹ * (p.constant + ξ • p.slope) * (CFC.sqrt p.slope)⁻¹ := rfl

theorem actual_centered_factorization (p : PositiveSlopePencil h) (ξ : ℝ) :
    p.detPolynomial = C p.slope.det *
      ∏ i, (X - C ξ + C (centeredDualEigenvalues p ξ i)) := by
  let q := whiteningData p ξ
  let S := CFC.sqrt p.slope
  have hsq : S * S = p.slope := Spectral.whiteningSqrt_sq q p.slope_posDef
  have hcong : S * centeredDualMatrix p ξ * S = p.constant + ξ • p.slope :=
    Spectral.whitening_congruence q p.slope_posDef
  have hsym : (centeredDualMatrix p ξ).IsHermitian :=
    Spectral.whitenedMatrix_isHermitian q
  have hmat (x : ℝ) : p.constant + x • p.slope =
      S * (centeredDualMatrix p ξ + (x-ξ) • 1) * S := by
    rw [Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hcong, hsq]
    simp only [sub_smul]
    abel
  apply Polynomial.funext
  intro x
  rw [p.eval_detPolynomial, hmat, Matrix.det_mul, Matrix.det_mul,
    det_add_smul_one_of_hermitian _ hsym]
  have hdet : S.det * S.det = p.slope.det := by rw [← Matrix.det_mul, hsq]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X]
  change S.det * (∏ i, (x - ξ + centeredDualEigenvalues p ξ i)) * S.det = _
  calc
    _ = (S.det * S.det) * ∏ i, (x - ξ + centeredDualEigenvalues p ξ i) := by ring
    _ = _ := by rw [hdet]

/-- Every root, with spectral multiplicity, is exactly ξ minus an actual
centered eigenvalue. No nonzero-eigenvalue condition is necessary. -/
theorem actual_centered_root_iff (p : PositiveSlopePencil h) (ξ : ℝ) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 ↔
      ∃ i, z = ((ξ - centeredDualEigenvalues p ξ i : ℝ) : ℂ) := by
  rw [actual_centered_factorization p ξ]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_X]
  have hd : (algebraMap ℝ ℂ) p.slope.det ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt p.slope_posDef.det_pos)
  rw [mul_eq_zero]
  simp only [hd, false_or, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    push_cast
    change z - (ξ : ℂ) + (centeredDualEigenvalues p ξ i : ℂ) = 0 at hi
    linear_combination hi
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    push_cast
    change (ξ : ℂ) - (centeredDualEigenvalues p ξ i : ℂ) -
      (ξ : ℂ) + (centeredDualEigenvalues p ξ i : ℂ) = 0
    ring

end ManuscriptChain.DualSpectral
