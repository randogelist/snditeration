import Zetahyperbolic.Section3.SignatureRestriction
import Zetahyperbolic.Section3.SpectralInertia
import Zetahyperbolic.Section3.PrincipalPencils

/-!
# Cauchy interlacing in eigenvalue-count form

At every real threshold, restricting a positive-base symmetric pencil to r
coordinates cannot increase its number of eigenvalues above the threshold,
and can decrease it by at most n-r. For consecutive principal sizes this is
precisely the multiplicity-sensitive Cauchy interlacing condition. Zero slopes
are included, so finite root degree loss causes no exception.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix QuadraticForm

namespace ManuscriptChain.Cauchy

variable {n r : ℕ}

/-- Coordinate inclusion as a rectangular matrix. -/
def inclusionMatrix (choose : Fin r → Fin n) : Matrix (Fin n) (Fin r) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id choose

theorem inclusion_congruence (choose : Fin r → Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (inclusionMatrix choose).transpose * A * inclusionMatrix choose =
      A.submatrix choose choose := by
  unfold inclusionMatrix
  rw [Matrix.transpose_submatrix, Matrix.transpose_one]
  change ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix choose (Equiv.refl (Fin n))) * A *
      ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix (Equiv.refl (Fin n)) choose) = _
  rw [Matrix.one_submatrix_mul choose (Equiv.refl (Fin n))]
  rw [Matrix.mul_submatrix_one (Equiv.refl (Fin n)) choose]
  rfl

theorem inclusion_injective (choose : Fin r → Fin n) (hchoose : Function.Injective choose) :
    Function.Injective (inclusionMatrix choose).mulVecLin := by
  have hleft : (inclusionMatrix choose).transpose * inclusionMatrix choose = 1 := by
    simpa [Matrix.mul_one, Matrix.submatrix_one choose hchoose] using
      inclusion_congruence choose (1 : Matrix (Fin n) (Fin n) ℝ)
  intro x y hxy
  have h := congrArg (fun v => (inclusionMatrix choose).transpose *ᵥ v) hxy
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using h

/-- Quadratic forms of principal submatrices are genuine injective pullbacks. -/
theorem principal_quadratic (choose : Fin r → Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.submatrix choose choose).toQuadraticForm' =
      A.toQuadraticForm'.comp (inclusionMatrix choose).mulVecLin := by
  rw [← inclusion_congruence choose A]
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    QuadraticMap.comp_apply, Matrix.toLinearMap₂'_apply', Matrix.mulVecLin_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- Principal restriction satisfies the dimension-correct positive-index bounds. -/
theorem principal_signature_bounds (choose : Fin r → Fin n)
    (hchoose : Function.Injective choose) (A : Matrix (Fin n) (Fin n) ℝ) :
    sigPos (A.submatrix choose choose).toQuadraticForm' ≤ sigPos A.toQuadraticForm' ∧
      sigPos A.toQuadraticForm' + r ≤
        sigPos (A.submatrix choose choose).toQuadraticForm' + n := by
  have h := SignatureRestriction.signature_comp_bounds A.toQuadraticForm'
    (inclusionMatrix choose).mulVecLin (inclusion_injective choose hchoose)
  simpa only [← principal_quadratic, Module.finrank_pi, Module.finrank_self,
    Fintype.card_fin, mul_one] using h

/-- The positive index of A-tI counts exactly the eigenvalues above t. -/
theorem shifted_signature (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (t : ℝ) :
    sigPos (A - t • 1).toQuadraticForm' = {i | t < hA.eigenvalues i}.ncard := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.eigenvectorUnitary
  have hU : U.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det U).mp (Unitary.isUnit_coe)).ne_zero
  have hUU : U * U.transpose = 1 := by
    simpa only [U, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hs : A = U * Matrix.diagonal hA.eigenvalues * U.transpose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, U] using hA.spectral_theorem
  have hdiag : Matrix.diagonal (fun i => hA.eigenvalues i - t) =
      Matrix.diagonal hA.eigenvalues - t • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, hij]
  have hconj : U * Matrix.diagonal (fun i => hA.eigenvalues i - t) * U.transpose =
      A - t • 1 := by
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, ← hs]
    simp [hUU]
  have h := SpectralInertia.sigPos_congruence
    (Matrix.diagonal (fun i => hA.eigenvalues i - t)) U.transpose
    (by simpa using hU)
  rw [Matrix.transpose_transpose, hconj, SpectralInertia.quadratic_diagonal,
    QuadraticForm.sigPos_weightedSumSquares] at h
  simpa only [sub_pos] using h.symm

/-- Generalized shifted signature is the actual whitened eigenvalue count. -/
theorem pencil_shifted_signature (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) (t : ℝ) :
    sigPos (p.direction - t • p.base).toQuadraticForm' =
      {i | t < Spectral.actualEigenvalues p i}.ncard := by
  let S := CFC.sqrt p.base
  have hS : S.transpose = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Spectral.whiteningSqrt_isHermitian p).eq
  have hconj : S.transpose * (Spectral.whitenedMatrix p - t • 1) * S =
      p.direction - t • p.base := by
    rw [hS, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [Spectral.whitening_congruence p hp, Spectral.whiteningSqrt_sq p hp]
  have h := SpectralInertia.sigPos_congruence
    (Spectral.whitenedMatrix p - t • 1) S
    (Spectral.whiteningSqrt_det_ne_zero p hp)
  rw [hconj, shifted_signature _ (Spectral.whitenedMatrix_isHermitian p) t] at h
  exact h.symm

/-- Restrict both forms of a symmetric affine pencil to the same coordinates. -/
def principalPencil (p : Spectral.SymmetricAffinePencil n)
    (choose : Fin r → Fin n) : Spectral.SymmetricAffinePencil r where
  center := p.center
  base := p.base.submatrix choose choose
  direction := p.direction.submatrix choose choose
  base_symmetric := p.base_symmetric.submatrix choose
  direction_symmetric := p.direction_symmetric.submatrix choose

/-- Full Cauchy interlacing, stated as exact all-threshold counting inequalities.
The gap is the codimension; in particular it is one for successive sizes. -/
theorem eigenvalue_count_interlacing (p : Spectral.SymmetricAffinePencil n)
    (hp : p.base.PosDef) (choose : Fin r → Fin n) (hchoose : Function.Injective choose)
    (t : ℝ) :
    {i | t < Spectral.actualEigenvalues (principalPencil p choose) i}.ncard ≤
      {i | t < Spectral.actualEigenvalues p i}.ncard ∧
    {i | t < Spectral.actualEigenvalues p i}.ncard + r ≤
      {i | t < Spectral.actualEigenvalues (principalPencil p choose) i}.ncard + n := by
  have h := principal_signature_bounds choose hchoose (p.direction - t • p.base)
  have hs : (p.direction - t • p.base).submatrix choose choose =
      (principalPencil p choose).direction - t • (principalPencil p choose).base := rfl
  have hp' : (principalPencil p choose).base.PosDef := hp.submatrix hchoose
  rw [hs, pencil_shifted_signature p hp,
    pencil_shifted_signature (principalPencil p choose) hp'] at h
  exact h

/-- Successive principal sizes differ by at most one eigenvalue above every threshold. -/
theorem consecutive_eigenvalue_count_interlacing
    (p : Spectral.SymmetricAffinePencil (r+1)) (hp : p.base.PosDef)
    (choose : Fin r → Fin (r+1)) (hchoose : Function.Injective choose) (t : ℝ) :
    {i | t < Spectral.actualEigenvalues (principalPencil p choose) i}.ncard ≤
      {i | t < Spectral.actualEigenvalues p i}.ncard ∧
    {i | t < Spectral.actualEigenvalues p i}.ncard ≤
      {i | t < Spectral.actualEigenvalues (principalPencil p choose) i}.ncard + 1 := by
  have h := eigenvalue_count_interlacing p hp choose hchoose t
  exact ⟨h.1, by omega⟩

/-- Actual manuscript specialization, with no rank assumption on the principal slope. -/
theorem actual_eigenvalue_count_interlacing (p : Real.Parameters) (hp : Real.Admissible p)
    (choose : Fin r → Fin p.h) (hchoose : Function.Injective choose) (t : ℝ) :
    {i | t < Spectral.actualEigenvalues (Principal.manuscriptPrincipalPencil p choose) i}.ncard ≤
      {i | t < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard ∧
    {i | t < Spectral.actualEigenvalues (Real.manuscriptPencil p) i}.ncard + r ≤
      {i | t < Spectral.actualEigenvalues (Principal.manuscriptPrincipalPencil p choose) i}.ncard + p.h :=
  eigenvalue_count_interlacing (Real.manuscriptPencil p) (GRAM_POSITIVE p hp) choose hchoose t

end ManuscriptChain.Cauchy

