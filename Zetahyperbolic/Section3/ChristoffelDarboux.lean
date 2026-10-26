import Zetahyperbolic.Section3.SpectralInertia
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Theorem 3.8(1): the actual orthogonal-polynomial pole kernel

The monic orthogonal family is constructed by LDL decomposition of the
actual positive Gram matrix. Its integral squared norms are proved positive,
and its Christoffel–Darboux sum equals the inverse-Gram evaluation kernel.
The pole matrix built from this sum has exactly the characteristic polynomial
of the manuscript's actual symmetric whitened matrix.

The generic LDL and integral proofs are adapted from the companion branch's
OrthogonalMomentKernel and OrthogonalMomentMeasure sources, with the finite
AB/BA identity from ImportedSection3/PoleKernel; all are rechecked here.
-/
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial MeasureTheory

namespace ManuscriptChain.ChristoffelDarboux


variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}

def orthogonalCoefficients (hG : G.PosDef) (i : Fin n) : Fin n → ℝ :=
  fun j => LDL.lowerInv hG i j / LDL.lowerInv hG i i

def monicPolynomial (hG : G.PosDef) (i : Fin n) : ℝ[X] :=
  Polynomial.ofFn n (orthogonalCoefficients hG i)

def squaredNorm (hG : G.PosDef) (i : Fin n) : ℝ :=
  LDL.diagEntries hG i / (LDL.lowerInv hG i i)^2

def kernel (hG : G.PosDef) (t u : ℝ) : ℝ :=
  ∑ i, (monicPolynomial hG i).eval t * (monicPolynomial hG i).eval u /
    squaredNorm hG i

theorem lower_diagonal_ne_zero (hG : G.PosDef) (i : Fin n) :
    LDL.lowerInv hG i i ≠ 0 := by
  have hd : (LDL.lowerInv hG).det ≠ 0 :=
    (Matrix.isUnit_det_of_invertible (LDL.lowerInv hG)).ne_zero
  rw [Matrix.det_of_isLowerTriangular _ (fun _ _ hij => LDL.lowerInv_triangular hG hij)] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

theorem diagonal_positive (hG : G.PosDef) (i : Fin n) :
    0 < LDL.diagEntries hG i := by
  have hd : (LDL.diag hG).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hG.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hG))
  simpa only [LDL.diag, Matrix.diagonal_apply_eq] using hd.diag_pos (i := i)

theorem squaredNorm_positive (hG : G.PosDef) (i : Fin n) :
    0 < squaredNorm hG i :=
  div_pos (diagonal_positive hG i) (sq_pos_of_ne_zero (lower_diagonal_ne_zero hG i))

theorem monicPolynomial_coeff_self (hG : G.PosDef) (i : Fin n) :
    (monicPolynomial hG i).coeff i.val = 1 := by
  simp [monicPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt,
    orthogonalCoefficients, lower_diagonal_ne_zero]

theorem monicPolynomial_coeff_above (hG : G.PosDef) (i : Fin n) {j : ℕ}
    (hij : i.val < j) : (monicPolynomial hG i).coeff j = 0 := by
  by_cases hj : j < n
  · rw [monicPolynomial, Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
    simp only [orthogonalCoefficients,
      LDL.lowerInv_triangular hG (show i < (⟨j, hj⟩ : Fin n) from hij), zero_div]
  · exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj)

theorem monicPolynomial_natDegree (hG : G.PosDef) (i : Fin n) :
    (monicPolynomial hG i).natDegree = i.val := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun _ hij => monicPolynomial_coeff_above hG i hij)
  · rw [monicPolynomial_coeff_self]
    exact one_ne_zero

theorem monicPolynomial_monic (hG : G.PosDef) (i : Fin n) :
    (monicPolynomial hG i).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [monicPolynomial_natDegree, monicPolynomial_coeff_self]

theorem inverse_diagonal (hG : G.PosDef) :
    (LDL.diag hG)⁻¹ = Matrix.diagonal (fun i => (LDL.diagEntries hG i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [LDL.diag, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [ne_of_gt (diagonal_positive hG i)]
  · simp [Matrix.diagonal_apply, hij]

theorem inverse_gram (hG : G.PosDef) :
    G⁻¹ = (LDL.lowerInv hG).transpose *
      Matrix.diagonal (fun i => (LDL.diagEntries hG i)⁻¹) * LDL.lowerInv hG := by
  calc
    G⁻¹ = (LDL.lower hG * LDL.diag hG * (LDL.lower hG)ᴴ)⁻¹ :=
      congrArg Inv.inv (LDL.lower_conj_diag hG).symm
    _ = _ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
        LDL.lower, Matrix.inv_inv, inverse_diagonal]
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

theorem monicPolynomial_eval (hG : G.PosDef) (i : Fin n) (t : ℝ) :
    (monicPolynomial hG i).eval t =
      (∑ j, LDL.lowerInv hG i j * t ^ j.val) / LDL.lowerInv hG i i := by
  rw [monicPolynomial, ManuscriptChain.Moments.eval_ofFn_eq_sum]
  simp only [orthogonalCoefficients, div_mul_eq_mul_div, Finset.sum_div]

theorem kernel_eq_inverseGram (hG : G.PosDef) (t u : ℝ) :
    kernel hG t u = (fun i : Fin n => t ^ i.val) ⬝ᵥ
      (G⁻¹ *ᵥ (fun i : Fin n => u ^ i.val)) := by
  rw [inverse_gram hG, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [kernel, dotProduct, Matrix.mulVec_diagonal, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i _
  rw [monicPolynomial_eval, monicPolynomial_eval]
  dsimp only [squaredNorm]
  field_simp [lower_diagonal_ne_zero hG i, ne_of_gt (diagonal_positive hG i)] <;> ring





theorem eval_ofFn_mul_eq_sum (c d : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n c).eval x * (Polynomial.ofFn n d).eval x =
      ∑ i, ∑ j, c i * d j * x ^ (i.val + j.val) := by
  rw [ManuscriptChain.Moments.eval_ofFn_eq_sum,
    ManuscriptChain.Moments.eval_ofFn_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem integrable_eval_ofFn_mul {μ : Measure ℝ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (c d : Fin n → ℝ) :
    Integrable (fun x => (Polynomial.ofFn n c).eval x * (Polynomial.ofFn n d).eval x) μ := by
  simp_rw [eval_ofFn_mul_eq_sum]
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hm i j).const_mul (c i * d j)))

theorem bilinear_eq_integral_product {μ : Measure ℝ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (hG : ∀ i j, G i j = ∫ x, x ^ (i.val + j.val) ∂μ)
    (c d : Fin n → ℝ) :
    c ⬝ᵥ (G *ᵥ d) =
      ∫ x, (Polynomial.ofFn n c).eval x * (Polynomial.ofFn n d).eval x ∂μ := by
  simp_rw [eval_ofFn_mul_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hm i j).const_mul (c i * d j)))]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hm i j).const_mul (c i * d j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, hG]
  ring

theorem bilinear_rescale (c d : Fin n → ℝ) (a b : ℝ) :
    (fun i => c i / a) ⬝ᵥ (G *ᵥ (fun j => d j / b)) =
      (c ⬝ᵥ (G *ᵥ d)) / (a*b) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem coefficient_pairing (hG : G.PosDef) (i j : Fin n) :
    orthogonalCoefficients hG i ⬝ᵥ (G *ᵥ orthogonalCoefficients hG j) =
      if i = j then squaredNorm hG i else 0 := by
  unfold orthogonalCoefficients
  rw [bilinear_rescale]
  have h := congrFun (congrFun (LDL.diag_eq_lowerInv_conj hG) i) j
  have he : (LDL.lowerInv hG i) ⬝ᵥ (G *ᵥ LDL.lowerInv hG j) =
      LDL.diag hG i j := by
    rw [h]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  by_cases hij : i = j
  · subst j
    simp [LDL.diag, squaredNorm, pow_two]
  · simp [LDL.diag, Matrix.diagonal_apply, hij]

theorem monicPolynomial_integral_product {μ : Measure ℝ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (hGram : ∀ i j, G i j = ∫ x, x ^ (i.val + j.val) ∂μ)
    (hG : G.PosDef) (i j : Fin n) :
    (∫ x, (monicPolynomial hG i).eval x * (monicPolynomial hG j).eval x ∂μ) =
      if i = j then squaredNorm hG i else 0 := by
  rw [monicPolynomial, monicPolynomial, ← bilinear_eq_integral_product hm hGram]
  exact coefficient_pairing hG i j

theorem kernel_eq_integral_normalized {μ : Measure ℝ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (hGram : ∀ i j, G i j = ∫ x, x ^ (i.val + j.val) ∂μ)
    (hG : G.PosDef) (t u : ℝ) :
    (∑ i, (monicPolynomial hG i).eval t * (monicPolynomial hG i).eval u /
      (∫ x, ((monicPolynomial hG i).eval x)^2 ∂μ)) =
      (fun i : Fin n => t ^ i.val) ⬝ᵥ (G⁻¹ *ᵥ (fun i => u ^ i.val)) := by
  calc
    _ = kernel hG t u := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [pow_two]
      rw [monicPolynomial_integral_product hm hGram]
      simp
    _ = _ := kernel_eq_inverseGram hG t u


end ManuscriptChain.ChristoffelDarboux

namespace ManuscriptChain.PoleKernel


/-- The pole-kernel matrix of the negative-lattice evaluation vectors. -/
def kernelMatrix {n : ℕ} (G V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  V.transpose * G⁻¹ * V

/-- General spectral operator in the pole (Christoffel–Darboux) basis. -/
def poleOperator {n : ℕ} (G V : Matrix (Fin n) (Fin n) ℝ)
    (γ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal γ * kernelMatrix G V

/-- Entire characteristic polynomial, with multiplicities, agrees in all dimensions. -/
theorem charpoly_relative_eq_pole {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) :
    (G⁻¹ * (V * Matrix.diagonal γ * V.transpose)).charpoly =
      (poleOperator G V γ).charpoly := by
  simpa only [poleOperator, kernelMatrix, Matrix.mul_assoc] using
    (Matrix.charpoly_mul_comm (G⁻¹ * V) (Matrix.diagonal γ * V.transpose))

/-- The first spectral power sum / relative trace is unchanged at the poles. -/
theorem trace_relative_eq_pole {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) ℝ) (γ : Fin n → ℝ) :
    (G⁻¹ * (V * Matrix.diagonal γ * V.transpose)).trace =
      (poleOperator G V γ).trace := by
  simpa only [poleOperator, kernelMatrix, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (G⁻¹ * V) (Matrix.diagonal γ * V.transpose))

/-- The pole-kernel matrix is literally the inverse-Gram evaluation pairing. -/
theorem kernelMatrix_entry {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    kernelMatrix G V a b =
      ∑ j : Fin n, ∑ i : Fin n, V i a * (G⁻¹) i j * V j b := by
  simp [kernelMatrix, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]


end ManuscriptChain.PoleKernel

namespace ManuscriptChain.ChristoffelDarboux

/-- The actual monic polynomial of each degree below h. -/
def actualPolynomial (p : Real.Parameters) (hp : Real.Admissible p) (i : Fin p.h) : ℝ[X] :=
  monicPolynomial (GRAM_POSITIVE p hp) i

/-- The actual Christoffel–Darboux sum in the manuscript. -/
def actualKernel (p : Real.Parameters) (hp : Real.Admissible p) (t u : ℝ) : ℝ :=
  ∑ i, (actualPolynomial p hp i).eval t * (actualPolynomial p hp i).eval u /
    (∫ x, ((actualPolynomial p hp i).eval x)^2 ∂(REALIZATION p hp).measure)

theorem actualPolynomial_monic (p : Real.Parameters) (hp : Real.Admissible p)
    (i : Fin p.h) : (actualPolynomial p hp i).Monic :=
  monicPolynomial_monic (GRAM_POSITIVE p hp) i

theorem actualPolynomial_degree (p : Real.Parameters) (hp : Real.Admissible p)
    (i : Fin p.h) : (actualPolynomial p hp i).natDegree = i.val :=
  monicPolynomial_natDegree (GRAM_POSITIVE p hp) i

/-- The constructed family is orthogonal for the concrete manuscript measure. -/
theorem actualPolynomial_orthogonal (p : Real.Parameters) (hp : Real.Admissible p)
    (i j : Fin p.h) :
    (∫ x, (actualPolynomial p hp i).eval x * (actualPolynomial p hp j).eval x
      ∂(REALIZATION p hp).measure) =
      if i = j then squaredNorm (GRAM_POSITIVE p hp) i else 0 :=
  monicPolynomial_integral_product (REALIZATION p hp).integrable_moments
    (REALIZATION p hp).moment_identity (GRAM_POSITIVE p hp) i j

/-- Every integral normalization is strictly positive. -/
theorem actualPolynomial_norm_pos (p : Real.Parameters) (hp : Real.Admissible p)
    (i : Fin p.h) :
    0 < ∫ x, ((actualPolynomial p hp i).eval x)^2 ∂(REALIZATION p hp).measure := by
  simp only [pow_two, actualPolynomial_orthogonal, if_true]
  exact squaredNorm_positive (GRAM_POSITIVE p hp) i

theorem actualKernel_inverseGram (p : Real.Parameters) (hp : Real.Admissible p)
    (t u : ℝ) :
    actualKernel p hp t u = (fun i : Fin p.h => t ^ i.val) ⬝ᵥ
      ((Real.gram p (Real.zeta p.weight))⁻¹ *ᵥ (fun i : Fin p.h => u ^ i.val)) :=
  kernel_eq_integral_normalized (REALIZATION p hp).integrable_moments
    (REALIZATION p hp).moment_identity (GRAM_POSITIVE p hp) t u

/-- The poles are exactly the negative integer squares in the manuscript. -/
def actualPoleNode (p : Real.Parameters) (a : Fin p.h) : ℝ :=
  (PoleDiagonalization.poleNode p a : ℝ)

theorem realPoleVandermonde_entry (p : Real.Parameters) (i a : Fin p.h) :
    SpectralInertia.realPoleVandermonde p i a = (actualPoleNode p a)^i.val := by
  simp [SpectralInertia.realPoleVandermonde, PoleDiagonalization.poleVandermonde,
    Matrix.map_apply, actualPoleNode]

/-- The signed pole matrix, with the *integral-normalized* CD kernel entries. -/
def actualPoleOperator (p : Real.Parameters) (hp : Real.Admissible p) :
    Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun a b => (PoleDiagonalization.poleWeight p a : ℝ) *
    actualKernel p hp (actualPoleNode p a) (actualPoleNode p b)

theorem actualPoleOperator_eq (p : Real.Parameters) (hp : Real.Admissible p) :
    actualPoleOperator p hp =
      PoleKernel.poleOperator (Real.gram p (Real.zeta p.weight))
        (SpectralInertia.realPoleVandermonde p)
        (fun a => (PoleDiagonalization.poleWeight p a : ℝ)) := by
  ext a b
  simp only [actualPoleOperator, PoleKernel.poleOperator, Matrix.diagonal_mul]
  congr 1
  rw [actualKernel_inverseGram, PoleKernel.kernelMatrix_entry]
  simp only [realPoleVandermonde_entry, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Symmetric normalization and the relative operator have the same characteristic polynomial. -/
theorem whitened_charpoly_eq_relative {n : ℕ} (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) :
    (Spectral.whitenedMatrix p).charpoly = (p.base⁻¹ * p.direction).charpoly := by
  let S := CFC.sqrt p.base
  have hs : S * S = p.base := by
    simpa [S, sq] using CFC.sq_sqrt p.base hp.posSemidef.nonneg
  have hi : S⁻¹ * S⁻¹ = p.base⁻¹ := by
    rw [← Matrix.mul_inv_rev, hs]
  change (S⁻¹ * p.direction * S⁻¹).charpoly = _
  rw [Matrix.charpoly_mul_comm (S⁻¹ * p.direction) S⁻¹, ← Matrix.mul_assoc, hi]

/-- Theorem 3.8(1): exact spectral coincidence, including algebraic multiplicities. -/
theorem actual_whitened_charpoly_eq_pole (p : Real.Parameters) (hp : Real.Admissible p) :
    (Spectral.whitenedMatrix (Real.manuscriptPencil p)).charpoly =
      (actualPoleOperator p hp).charpoly := by
  rw [whitened_charpoly_eq_relative (Real.manuscriptPencil p) (GRAM_POSITIVE p hp),
    actualPoleOperator_eq]
  change ((Real.gram p (Real.zeta p.weight))⁻¹ * Real.derivativeMatrix p).charpoly = _
  rw [SpectralInertia.real_direction_factorization]
  exact PoleKernel.charpoly_relative_eq_pole _ _ _

theorem actual_whitened_roots_eq_pole (p : Real.Parameters) (hp : Real.Admissible p) :
    (Spectral.whitenedMatrix (Real.manuscriptPencil p)).charpoly.roots =
      (actualPoleOperator p hp).charpoly.roots :=
  congrArg Polynomial.roots (actual_whitened_charpoly_eq_pole p hp)

end ManuscriptChain.ChristoffelDarboux
