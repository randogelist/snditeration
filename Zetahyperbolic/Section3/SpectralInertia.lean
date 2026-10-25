import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Zetahyperbolic.Section3.ActualSpectrum
import Zetahyperbolic.Section3.PoleSigns
import Zetahyperbolic.Section3.PoleSignCounts
import Mathlib.Tactic
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix
namespace ManuscriptChain.SpectralInertia
variable {n : ℕ}

def matrixEquiv (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  { C.mulVecLin with
    invFun := fun x => C⁻¹ *ᵥ x
    left_inv := fun x => by
      change C⁻¹ *ᵥ (C *ᵥ x) = x
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC), one_mulVec]
    right_inv := fun x => by
      change C *ᵥ (C⁻¹ *ᵥ x) = x
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr hC), one_mulVec] }

theorem quadratic_congruence (A C : Matrix (Fin n) (Fin n) ℝ) :
    (C.transpose * A * C).toQuadraticForm' = A.toQuadraticForm'.comp C.mulVecLin := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    QuadraticMap.comp_apply, Matrix.toLinearMap₂'_apply', Matrix.mulVecLin_apply]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem quadratic_equivalent_congruence (A C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.det ≠ 0) :
    A.toQuadraticForm'.Equivalent (C.transpose * A * C).toQuadraticForm' := by
  rw [quadratic_congruence]
  exact ⟨QuadraticMap.isometryEquivOfCompLinearEquiv A.toQuadraticForm' (matrixEquiv C hC)⟩

theorem quadratic_diagonal (w : Fin n → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.mulVec_diagonal, QuadraticMap.weightedSumSquares_apply,
    dotProduct, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem sigPos_congruence (A C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    sigPos A.toQuadraticForm' = sigPos (C.transpose * A * C).toQuadraticForm' :=
  (quadratic_equivalent_congruence A C hC).sigPos_eq

theorem sigNeg_congruence (A C : Matrix (Fin n) (Fin n) ℝ) (hC : C.det ≠ 0) :
    sigNeg A.toQuadraticForm' = sigNeg (C.transpose * A * C).toQuadraticForm' :=
  (quadratic_equivalent_congruence A C hC).sigNeg_eq


theorem signature_eq_eigenvalue_counts (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    sigPos A.toQuadraticForm' = {i | 0 < hA.eigenvalues i}.ncard ∧
    sigNeg A.toQuadraticForm' = {i | hA.eigenvalues i < 0}.ncard := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  have hU : U.det ≠ 0 := by
    exact ((Matrix.isUnit_iff_isUnit_det U).mp (Unitary.isUnit_coe)).ne_zero
  have hs : A = U * Matrix.diagonal hA.eigenvalues * U.transpose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, U] using hA.spectral_theorem
  have hpos := sigPos_congruence (Matrix.diagonal hA.eigenvalues) U.transpose
    (by simpa using hU)
  have hneg := sigNeg_congruence (Matrix.diagonal hA.eigenvalues) U.transpose
    (by simpa using hU)
  simp only [Matrix.transpose_transpose, ← hs, quadratic_diagonal] at hpos hneg
  exact ⟨hpos.symm.trans QuadraticForm.sigPos_weightedSumSquares,
    hneg.symm.trans QuadraticForm.sigNeg_weightedSumSquares⟩


theorem whitening_signature (p : Spectral.SymmetricAffinePencil n)
    (positive : p.base.PosDef) :
    sigPos (Spectral.whitenedMatrix p).toQuadraticForm' = sigPos p.direction.toQuadraticForm' ∧
    sigNeg (Spectral.whitenedMatrix p).toQuadraticForm' = sigNeg p.direction.toQuadraticForm' := by
  have hs : (CFC.sqrt p.base).transpose = CFC.sqrt p.base := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Spectral.whiteningSqrt_isHermitian p).eq
  have hpos := sigPos_congruence (Spectral.whitenedMatrix p) (CFC.sqrt p.base)
    (Spectral.whiteningSqrt_det_ne_zero p positive)
  have hneg := sigNeg_congruence (Spectral.whitenedMatrix p) (CFC.sqrt p.base)
    (Spectral.whiteningSqrt_det_ne_zero p positive)
  rw [hs, Spectral.whitening_congruence p positive] at hpos hneg
  exact ⟨hpos, hneg⟩

def realPoleVandermonde (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  (PoleDiagonalization.poleVandermonde p).map (Rat.castHom ℝ)

theorem realPoleVandermonde_det_ne_zero (p : Real.Parameters) :
    (realPoleVandermonde p).det ≠ 0 := by
  have h : ((PoleDiagonalization.poleVandermonde p).det : ℝ) ≠ 0 := by
    exact_mod_cast PoleDiagonalization.poleVandermonde_det_ne_zero p
  rw [Rat.cast_det] at h
  exact h

theorem real_direction_factorization (p : Real.Parameters) :
    Real.derivativeMatrix p = realPoleVandermonde p *
      Matrix.diagonal (fun i => (PoleDiagonalization.poleWeight p i : ℝ)) *
      (realPoleVandermonde p).transpose := by
  have h := congrArg (fun A : Matrix (Fin p.h) (Fin p.h) ℚ => A.map (Rat.castHom ℝ))
    (PoleDiagonalization.rationalDerivativeMatrix_factorization p)
  simpa only [Matrix.map_mul, Matrix.diagonal_map (map_zero (Rat.castHom ℝ)), Matrix.transpose_map,
    realPoleVandermonde, PoleDiagonalization.rationalDerivativeMatrix, Real.derivativeMatrix]
    using h

theorem direction_signature (p : Real.Parameters) (hm : 0 < p.m) :
    sigPos (Real.derivativeMatrix p).toQuadraticForm' =
      {i : Fin p.h | Even (p.N + i.val)}.ncard ∧
    sigNeg (Real.derivativeMatrix p).toQuadraticForm' =
      {i : Fin p.h | Odd (p.N + i.val)}.ncard := by
  let w : Fin p.h → ℝ := fun i => (PoleDiagonalization.poleWeight p i : ℝ)
  have hpos := sigPos_congruence (Matrix.diagonal w) (realPoleVandermonde p).transpose
    (by simpa using realPoleVandermonde_det_ne_zero p)
  have hneg := sigNeg_congruence (Matrix.diagonal w) (realPoleVandermonde p).transpose
    (by simpa using realPoleVandermonde_det_ne_zero p)
  have hfac : realPoleVandermonde p * Matrix.diagonal w *
      (realPoleVandermonde p).transpose = Real.derivativeMatrix p :=
    (real_direction_factorization p).symm
  simp only [Matrix.transpose_transpose] at hpos hneg
  rw [hfac, quadratic_diagonal, QuadraticForm.sigPos_weightedSumSquares] at hpos
  rw [hfac, quadratic_diagonal, QuadraticForm.sigNeg_weightedSumSquares] at hneg
  have hwp : {i : Fin p.h | 0 < w i} = {i : Fin p.h | Even (p.N + i.val)} := by
    ext i
    simpa only [Set.mem_ofPred_eq, w, Rat.cast_pos] using
      PoleDiagonalization.poleWeight_pos_iff p hm i
  have hwn : {i : Fin p.h | w i < 0} = {i : Fin p.h | Odd (p.N + i.val)} := by
    ext i
    simpa only [Set.mem_ofPred_eq, w, Rat.cast_lt_zero] using
      PoleDiagonalization.poleWeight_neg_iff p hm i
  rw [hwp] at hpos
  rw [hwn] at hneg
  exact ⟨hpos.symm, hneg.symm⟩

/-- Sylvester inertia for the actual whitened matrix: positive/negative eigenvalues
are counted with algebraic multiplicity by the alternating pole signs. -/
theorem actual_inertia (p : Real.Parameters) (hp : Real.Admissible p) :
    {i | 0 < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard =
      {i : Fin p.h | Even (p.N + i.val)}.ncard ∧
    {i | Spectral.actualEigenvalues (Real.manuscriptPencil p) i < 0}.ncard =
      {i : Fin p.h | Odd (p.N + i.val)}.ncard := by
  have he := signature_eq_eigenvalue_counts (Spectral.whitenedMatrix (Real.manuscriptPencil p))
    (Spectral.whitenedMatrix_isHermitian _)
  have hw := whitening_signature (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
  have hd := direction_signature p hp.m_pos
  exact ⟨he.1.symm.trans (hw.1.trans hd.1), he.2.symm.trans (hw.2.trans hd.2)⟩

/-- Exact root-side counts, indexing roots with their spectral multiplicity. -/
theorem actual_root_side_counts (p : Real.Parameters) (hp : Real.Admissible p) :
    {i | Real.zeta p.weight -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹ < Real.zeta p.weight}.ncard =
      {i : Fin p.h | Even (p.N + i.val)}.ncard ∧
    {i | Real.zeta p.weight < Real.zeta p.weight -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹}.ncard =
      {i : Fin p.h | Odd (p.N + i.val)}.ncard := by
  have hright (a b : ℝ) : a < a - b⁻¹ ↔ b < 0 := by
    have h : a < a - b⁻¹ ↔ b⁻¹ < 0 := by constructor <;> intro hh <;> linarith
    exact h.trans inv_neg''
  simpa only [sub_lt_self_iff, inv_pos, hright] using actual_inertia p hp


/-- Evaluated inertia counts for every admissible manuscript pencil. -/
theorem actual_inertia_formula (p : Real.Parameters) (hp : Real.Admissible p) :
    {i | 0 < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard =
      (if Even p.N then (p.h + 1) / 2 else p.h / 2) ∧
    {i | Spectral.actualEigenvalues (Real.manuscriptPencil p) i < 0}.ncard =
      (if Even p.N then p.h / 2 else (p.h + 1) / 2) := by
  simpa only [PoleSignCounts.even_fin_count, PoleSignCounts.odd_fin_count]
    using actual_inertia p hp

theorem actual_root_side_formula (p : Real.Parameters) (hp : Real.Admissible p) :
    {i | Real.zeta p.weight -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹ < Real.zeta p.weight}.ncard =
      (if Even p.N then (p.h + 1) / 2 else p.h / 2) ∧
    {i | Real.zeta p.weight < Real.zeta p.weight -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹}.ncard =
      (if Even p.N then p.h / 2 else (p.h + 1) / 2) := by
  simpa only [PoleSignCounts.even_fin_count, PoleSignCounts.odd_fin_count]
    using actual_root_side_counts p hp

theorem weightFive_admissible (n : ℕ) (hn : 0 < n) :
    Real.Admissible (PoleDiagonalization.weightFiveParameters n) := by
  constructor
  · norm_num [PoleDiagonalization.weightFiveParameters]
  · norm_num [PoleDiagonalization.weightFiveParameters]
  · change 0 < 3 * n
    omega
  · change 3 * n < 30 * n
    omega

/-- Weight-five inertia: floor(27n/2) positive and ceil(27n/2) negative eigenvalues. -/
theorem weightFive_actual_inertia (n : ℕ) (hn : 0 < n) :
    let p := PoleDiagonalization.weightFiveParameters n
    {i | 0 < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard = 27 * n / 2 ∧
    {i | Spectral.actualEigenvalues (Real.manuscriptPencil p) i < 0}.ncard =
      (27 * n + 1) / 2 := by
  have h := actual_inertia (PoleDiagonalization.weightFiveParameters n)
    (weightFive_admissible n hn)
  simpa only [PoleSignCounts.weightFive_even_count, PoleSignCounts.weightFive_odd_count] using h

/-- Theorem 3.3(3), counting roots with their spectral multiplicities. -/
theorem weightFive_root_side_counts (n : ℕ) (hn : 0 < n) :
    let p := PoleDiagonalization.weightFiveParameters n
    {i | Real.zeta 5 -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹ < Real.zeta 5}.ncard =
      27 * n / 2 ∧
    {i | Real.zeta 5 < Real.zeta 5 -
      (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹}.ncard =
      (27 * n + 1) / 2 := by
  have h := actual_root_side_counts (PoleDiagonalization.weightFiveParameters n)
    (weightFive_admissible n hn)
  rw [PoleSignCounts.weightFive_even_count, PoleSignCounts.weightFive_odd_count] at h
  exact h

end ManuscriptChain.SpectralInertia
