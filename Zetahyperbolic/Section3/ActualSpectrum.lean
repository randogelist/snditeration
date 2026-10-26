import Zetahyperbolic.Section3.Unconditional
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The actual whitened Hankel spectrum

The spectral factors are the eigenvalues of the explicitly defined matrix
`(sqrt G)⁻¹ * M * (sqrt G)⁻¹`, not an unspecified choice of a factorization.
The final manuscript specialization requires only admissible parameters.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace ManuscriptChain.Spectral

variable {n : ℕ}

/-- The paper's normalized symmetric slope matrix. -/
def whitenedMatrix (p : SymmetricAffinePencil n) : Matrix (Fin n) (Fin n) ℝ :=
  (CFC.sqrt p.base)⁻¹ * p.direction * (CFC.sqrt p.base)⁻¹

theorem whiteningSqrt_sq (p : SymmetricAffinePencil n) (positive : p.base.PosDef) :
    CFC.sqrt p.base * CFC.sqrt p.base = p.base := by
  simpa [sq] using CFC.sq_sqrt p.base positive.posSemidef.nonneg

theorem whiteningSqrt_isHermitian (p : SymmetricAffinePencil n) :
    (CFC.sqrt p.base).IsHermitian :=
  (CFC.sqrt_nonneg p.base).posSemidef.isHermitian

theorem whiteningSqrt_det_ne_zero (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) : (CFC.sqrt p.base).det ≠ 0 := by
  have h := congrArg Matrix.det (whiteningSqrt_sq p positive)
  rw [Matrix.det_mul] at h
  intro hz
  simp [hz] at h
  exact (ne_of_gt positive.det_pos) h.symm

theorem whitenedMatrix_isHermitian (p : SymmetricAffinePencil n) :
    (whitenedMatrix p).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul ((CFC.sqrt p.base)⁻¹)
    (Matrix.isHermitian_iff_isSymm.mpr p.direction_symmetric)
  simpa only [whitenedMatrix, (whiteningSqrt_isHermitian p).inv.eq] using h

theorem whitenedMatrix_det_ne_zero (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0) :
    (whitenedMatrix p).det ≠ 0 := by
  have hunit : IsUnit (CFC.sqrt p.base).det :=
    isUnit_iff_ne_zero.mpr (whiteningSqrt_det_ne_zero p positive)
  have hinv : ((CFC.sqrt p.base)⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det _ hunit).ne_zero
  unfold whitenedMatrix
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hinv direction_nonzero) hinv

theorem whitening_congruence (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) :
    CFC.sqrt p.base * whitenedMatrix p * CFC.sqrt p.base = p.direction := by
  let S := CFC.sqrt p.base
  have hunit : IsUnit S.det :=
    isUnit_iff_ne_zero.mpr (whiteningSqrt_det_ne_zero p positive)
  change S * (S⁻¹ * p.direction * S⁻¹) * S = p.direction
  calc
    S * (S⁻¹ * p.direction * S⁻¹) * S =
        (S * S⁻¹) * p.direction * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
    _ = p.direction := by
      rw [Matrix.mul_nonsing_inv S hunit, Matrix.nonsing_inv_mul S hunit]
      simp

theorem matrixAt_whitening (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (x : ℝ) :
    p.matrixAt x = CFC.sqrt p.base *
      (1 + (x - p.center) • whitenedMatrix p) * CFC.sqrt p.base := by
  calc
    p.matrixAt x = CFC.sqrt p.base * CFC.sqrt p.base +
        (x - p.center) • (CFC.sqrt p.base * whitenedMatrix p * CFC.sqrt p.base) := by
      rw [whiteningSqrt_sq p positive, whitening_congruence p positive]
      rfl
    _ = _ := by simp [Matrix.mul_add, Matrix.add_mul]

/-- These are the actual Mathlib eigenvalues of the paper's matrix B. -/
def actualEigenvalues (p : SymmetricAffinePencil n) : Fin n → ℝ :=
  (whitenedMatrix_isHermitian p).eigenvalues

theorem actualEigenvalues_ne_zero (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (i : Fin n) : actualEigenvalues p i ≠ 0 := by
  intro hi
  apply whitenedMatrix_det_ne_zero p positive direction_nonzero
  rw [(whitenedMatrix_isHermitian p).det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

/-- The determinant product uses the spectrum of the explicit whitened matrix. -/
theorem detPolynomial_actual_factorization (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) :
    p.detPolynomial = C p.base.det *
      ∏ i, spectralFactor p.center (actualEigenvalues p i) := by
  apply Polynomial.funext
  intro x
  rw [p.eval_detPolynomial, SymmetricAffinePencil.detValue, matrixAt_whitening p positive]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hdetbase : (CFC.sqrt p.base).det * (CFC.sqrt p.base).det = p.base.det := by
    rw [← Matrix.det_mul, whiteningSqrt_sq p positive]
  rw [det_one_add_smul_of_hermitian (whitenedMatrix p) (whitenedMatrix_isHermitian p)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    eval_spectralFactor, actualEigenvalues]
  calc
    (CFC.sqrt p.base).det *
        (∏ i, (1 + (x - p.center) * (whitenedMatrix_isHermitian p).eigenvalues i)) *
        (CFC.sqrt p.base).det =
      ((CFC.sqrt p.base).det * (CFC.sqrt p.base).det) *
        ∏ i, (1 + (x - p.center) * (whitenedMatrix_isHermitian p).eigenvalues i) := by ring
    _ = _ := by rw [hdetbase]

/-- A constructed spectral factorization with its eigenvalue field fixed explicitly. -/
def actualRootFactorization (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0) :
    RootFactorization p where
  beta := actualEigenvalues p
  beta_ne_zero := actualEigenvalues_ne_zero p positive direction_nonzero
  base_det_ne_zero := ne_of_gt positive.det_pos
  factorization := detPolynomial_actual_factorization p positive

@[simp] theorem actualRootFactorization_beta (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0) :
    (actualRootFactorization p positive direction_nonzero).beta = actualEigenvalues p := rfl

theorem actual_complex_root_iff (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 ↔
      ∃ i, z = ((p.center - (actualEigenvalues p i)⁻¹ : ℝ) : ℂ) := by
  let c := actualRootFactorization p positive direction_nonzero
  constructor
  · intro hz
    exact c.complex_root_location z hz
  · rintro ⟨i, rfl⟩
    have he := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (c.root i)
      (p := p.detPolynomial)
    have hroot : c.root i = p.center - (actualEigenvalues p i)⁻¹ := rfl
    simp only [Complex.coe_algebraMap, c.eval_root, map_zero] at he
    rw [hroot] at he
    exact he


/-- Explicit ℓ² operator norm, through the Euclidean-space continuous linear map. -/
def actualOperatorNorm (p : SymmetricAffinePencil n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (whitenedMatrix p)‖

open scoped Matrix.Norms.L2Operator in
theorem actualOperatorNorm_eq_eigenvalueNorm (p : SymmetricAffinePencil n) :
    actualOperatorNorm p = ‖actualEigenvalues p‖ := by
  unfold actualOperatorNorm actualEigenvalues
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  conv_lhs => rw [(whitenedMatrix_isHermitian p).spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, Matrix.l2_opNorm_diagonal]

theorem actualEigenvalues_abs_le_operatorNorm (p : SymmetricAffinePencil n) (i : Fin n) :
    |actualEigenvalues p i| ≤ actualOperatorNorm p := by
  rw [actualOperatorNorm_eq_eigenvalueNorm]
  exact norm_le_pi_norm (actualEigenvalues p) i

theorem actualOperatorNorm_pos (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0) (hn : 0 < n) :
    0 < actualOperatorNorm p := by
  let i : Fin n := ⟨0, hn⟩
  exact lt_of_lt_of_le
    (abs_pos.mpr (actualEigenvalues_ne_zero p positive direction_nonzero i))
    (actualEigenvalues_abs_le_operatorNorm p i)

theorem actualOperatorNorm_attained (p : SymmetricAffinePencil n) (hn : 0 < n) :
    ∃ i, |actualEigenvalues p i| = actualOperatorNorm p := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (actualEigenvalues p)).1
  exact ⟨i, by simpa only [actualOperatorNorm_eq_eigenvalueNorm, Real.norm_eq_abs] using hi⟩

theorem actual_complex_root_distance (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    1 / actualOperatorNorm p ≤ ‖z - (p.center : ℂ)‖ := by
  let c := actualRootFactorization p positive direction_nonzero
  obtain ⟨i, rfl⟩ := c.complex_root_location z hz
  have h := c.root_distance_lower_bound (actualOperatorNorm p)
    (actualEigenvalues_abs_le_operatorNorm p) i
  simpa [← Complex.ofReal_sub] using h

theorem actual_operator_zero_free_disk (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (z : ℂ) (hz : ‖z - (p.center : ℂ)‖ < 1 / actualOperatorNorm p) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial ≠ 0 := by
  intro hroot
  exact (not_lt_of_ge (actual_complex_root_distance p positive direction_nonzero z hroot)) hz

theorem actual_operator_boundary_root (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0) (hn : 0 < n) :
    ∃ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 ∧
      ‖z - (p.center : ℂ)‖ = 1 / actualOperatorNorm p := by
  let c := actualRootFactorization p positive direction_nonzero
  obtain ⟨i, hi⟩ := actualOperatorNorm_attained p hn
  refine ⟨(c.root i : ℂ), ?_, ?_⟩
  · exact (actual_complex_root_iff p positive direction_nonzero _).mpr ⟨i, rfl⟩
  · have hd := c.root_distance i
    change |c.root i - p.center| = 1 / |actualEigenvalues p i| at hd
    rw [hi] at hd
    simpa [← Complex.ofReal_sub] using hd

end ManuscriptChain.Spectral

namespace ManuscriptChain

/-- Theorem 3.1 with the actual G^(-1/2) M G^(-1/2) matrix exposed. -/
theorem ACTUAL_SPECTRAL_FACTORIZATION (p : Real.Parameters) (hp : Real.Admissible p) :
    let q := Real.manuscriptPencil p
    (Spectral.whitenedMatrix q).IsHermitian ∧
    (Spectral.whitenedMatrix q).det ≠ 0 ∧
    (∀ i, Spectral.actualEigenvalues q i ≠ 0) ∧
    q.detPolynomial = C q.base.det *
      ∏ i, Spectral.spectralFactor q.center (Spectral.actualEigenvalues q i) := by
  exact ⟨Spectral.whitenedMatrix_isHermitian _,
    Spectral.whitenedMatrix_det_ne_zero _ (GRAM_POSITIVE p hp)
      (General.derivative_nonsingular p),
    Spectral.actualEigenvalues_ne_zero _ (GRAM_POSITIVE p hp)
      (General.derivative_nonsingular p),
    Spectral.detPolynomial_actual_factorization _ (GRAM_POSITIVE p hp)⟩

/-- The actual determinant roots are ζ(s) minus reciprocals of the actual B-eigenvalues. -/
theorem ACTUAL_SPECTRAL_ROOTS (p : Real.Parameters) (hp : Real.Admissible p) (z : ℂ) :
    General.ComplexRoot p z ↔ ∃ i,
      z = ((Real.zeta p.weight -
        (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹ : ℝ) : ℂ) := by
  change Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.delta p) = 0 ↔ _
  rw [← General.complex_eval_transport]
  exact Spectral.actual_complex_root_iff (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
    (General.derivative_nonsingular p) z


/-- Theorem 3.1's sharp radius is the inverse actual ℓ² operator norm of B. -/
theorem ACTUAL_OPERATOR_ZERO_FREE_DISK (p : Real.Parameters) (hp : Real.Admissible p) :
    let radius := 1 / Spectral.actualOperatorNorm (Real.manuscriptPencil p)
    0 < radius ∧
    (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ < radius → ¬ General.ComplexRoot p z) ∧
    (∃ z : ℂ, General.ComplexRoot p z ∧
      ‖z - (Real.zeta p.weight : ℂ)‖ = radius) := by
  let q := Real.manuscriptPencil p
  have hn : 0 < p.h := Nat.sub_pos_of_lt hp.N_lt_K
  have hpos := GRAM_POSITIVE p hp
  have hdir := General.derivative_nonsingular p
  refine ⟨one_div_pos.mpr (Spectral.actualOperatorNorm_pos q hpos hdir hn), ?_, ?_⟩
  · intro z hz hroot
    have hr : Polynomial.eval₂ (algebraMap ℝ ℂ) z q.detPolynomial = 0 := by
      rw [General.complex_eval_transport]
      exact hroot
    exact Spectral.actual_operator_zero_free_disk q hpos hdir z hz hr
  · obtain ⟨z, hz, hd⟩ := Spectral.actual_operator_boundary_root q hpos hdir hn
    refine ⟨z, ?_, hd⟩
    rw [General.complex_eval_transport] at hz
    exact hz

end ManuscriptChain
