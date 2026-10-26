import Zetahyperbolic.Section3.Unconditional

/-!
# Actual principal Hankel pencils, including singular directions

Every principal base submatrix of the admissible manuscript pencil is positive
at the zeta center. Its determinant polynomial has only real complex roots,
even if the principal direction is singular and its degree drops. This proves
the principal-root reality component of Theorem 3.4, not interlacing.

The general square-root whitening proof is migrated from
`Theorem_3_4_Actual_Principal_Pencil_Reality.lean` in archive
`ZETAHYPERBOLIC_PAPER_CHRONOLOGY_v0_6_4_0_CROSS_CHAPTER_FINITE_BRIDGES_433.zip`.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace ManuscriptChain.Principal

open ManuscriptChain.Spectral

/-- Positive-definite base implies a real spectral factorization even if
`det direction = 0`. This generalizes the already proved Theorem 3.1 lemma
by deliberately dropping its derivative-invertibility premise. -/
theorem factorization_without_direction_invertibility {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef) :
    ∃ beta : Fin n → ℝ,
      p.detPolynomial =
        Polynomial.C (Matrix.det p.base) *
          ∏ i, spectralFactor p.center (beta i) := by
  let S := CFC.sqrt p.base
  have hSsq : S * S = p.base := by
    simpa [S, sq] using CFC.sq_sqrt p.base positive.posSemidef.nonneg
  have hSsymm : S.IsHermitian :=
    (CFC.sqrt_nonneg p.base).posSemidef.isHermitian
  have hbase : Matrix.det p.base ≠ 0 := ne_of_gt positive.det_pos
  have hSdet : Matrix.det S ≠ 0 := by
    have h := congrArg Matrix.det hSsq
    rw [Matrix.det_mul] at h
    intro hz
    simp [hz] at h
    exact hbase h.symm
  have hSunit : IsUnit (Matrix.det S) := isUnit_iff_ne_zero.mpr hSdet
  let B := S⁻¹ * p.direction * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.direction_symmetric)
    simpa only [hSsymm.inv.eq] using h
  have hconj : S * B * S = p.direction := by
    dsimp only [B]
    calc
      S * (S⁻¹ * p.direction * S⁻¹) * S =
          (S * S⁻¹) * p.direction * (S⁻¹ * S) := by
            simp only [Matrix.mul_assoc]
      _ = p.direction := by
        rw [Matrix.mul_nonsing_inv S hSunit, Matrix.nonsing_inv_mul S hSunit]
        simp
  have hpencil (x : ℝ) :
      p.matrixAt x = S * (1 + (x - p.center) • B) * S := by
    calc
      p.matrixAt x = S * S + (x - p.center) • (S * B * S) := by
        rw [hSsq, hconj]
        rfl
      _ = S * (1 + (x - p.center) • B) * S := by
        simp [Matrix.mul_add, Matrix.add_mul]
  refine ⟨hBsymm.eigenvalues, ?_⟩
  apply Polynomial.funext
  intro x
  rw [p.eval_detPolynomial, SymmetricAffinePencil.detValue, hpencil]
  rw [Matrix.det_mul, Matrix.det_mul]
  have hdetbase : Matrix.det S * Matrix.det S = Matrix.det p.base := by
    rw [← Matrix.det_mul, hSsq]
  rw [ManuscriptChain.Spectral.det_one_add_smul_of_hermitian B hBsymm]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    ManuscriptChain.Spectral.eval_spectralFactor]
  calc
    Matrix.det S * (∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i)) *
        Matrix.det S = (Matrix.det S * Matrix.det S) *
          ∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i) := by ring
    _ = _ := by rw [hdetbase]

/-- Any complex root of a positive-base symmetric pencil lies on the REAL
axis, with no assumption on its derivative's rank. -/
theorem every_complex_root_real_without_direction_invertibility {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 := by
  obtain ⟨beta, hfactor⟩ :=
    factorization_without_direction_invertibility p positive
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      ((Matrix.det p.base : ℝ) : ℂ) *
        ∏ i, (1 + (z - (p.center : ℂ)) * (beta i : ℂ)) := by
    rw [hfactor]
    simp [spectralFactor, Polynomial.eval₂_finsetProd]
  rw [heval] at hz
  have hd : ((Matrix.det p.base : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt positive.det_pos)
  have hp := (mul_eq_zero.mp hz).resolve_left hd
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
  have hb : beta i ≠ 0 := by
    intro hzero
    simp [hzero] at hi
  have hb_complex : (beta i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hx := (linear_factor_eq_zero_iff (p.center : ℂ)
    (beta i : ℂ) z hb_complex).mp hi
  rw [hx]
  simp

/-- Select a principal subpencil with the manuscript's actual base and direction. -/
def manuscriptPrincipalPencil (p : Real.Parameters)
    {r : ℕ} (choose : Fin r → Fin p.h) : SymmetricAffinePencil r where
  center := Real.zeta p.weight
  base := (Real.gram p (Real.zeta p.weight)).submatrix choose choose
  direction := (Real.derivativeMatrix p).submatrix choose choose
  base_symmetric := (Real.gram_symmetric p _).submatrix choose
  direction_symmetric := (Real.derivativeMatrix_symmetric p).submatrix choose

/-- Every injectively selected actual principal base is positive definite. -/
theorem principal_base_posDef (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (choose : Fin r → Fin p.h) (hchoose : Function.Injective choose) :
    (manuscriptPrincipalPencil p choose).base.PosDef :=
  (GRAM_POSITIVE p hp).submatrix hchoose

/-- Arbitrary actual principal minors are strictly positive at the zeta center. -/
theorem principal_center_positive (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (choose : Fin r → Fin p.h) (hchoose : Function.Injective choose) :
    0 < (manuscriptPrincipalPencil p choose).detPolynomial.eval (Real.zeta p.weight) := by
  change 0 < (manuscriptPrincipalPencil p choose).detPolynomial.eval
    (manuscriptPrincipalPencil p choose).center
  rw [SymmetricAffinePencil.eval_detPolynomial_center]
  exact (principal_base_posDef p hp choose hchoose).det_pos

/-- In particular, principal determinant polynomials never vanish identically. -/
theorem principal_detPolynomial_ne_zero (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (choose : Fin r → Fin p.h) (hchoose : Function.Injective choose) :
    (manuscriptPrincipalPencil p choose).detPolynomial ≠ 0 := by
  intro hz
  have hpos := principal_center_positive p hp choose hchoose
  rw [hz, Polynomial.eval_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Every actual principal-minor root is real, without any rank assumption on its slope. -/
theorem principal_roots_real (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (choose : Fin r → Fin p.h) (hchoose : Function.Injective choose)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (manuscriptPrincipalPencil p choose).detPolynomial = 0) : z.im = 0 :=
  every_complex_root_real_without_direction_invertibility
    (manuscriptPrincipalPencil p choose) (principal_base_posDef p hp choose hchoose) z hz

/-- Evaluation is the determinant of the actual principal Hankel matrix. -/
theorem principal_matrixAt (p : Real.Parameters) {r : ℕ}
    (choose : Fin r → Fin p.h) (x : ℝ) :
    (manuscriptPrincipalPencil p choose).matrixAt x =
      (Real.gram p x).submatrix choose choose := by
  change ((Real.manuscriptPencil p).matrixAt x).submatrix choose choose = _
  rw [Real.manuscriptPencil_matrixAt]

theorem principal_eval_detPolynomial (p : Real.Parameters) {r : ℕ}
    (choose : Fin r → Fin p.h) (x : ℝ) :
    (manuscriptPrincipalPencil p choose).detPolynomial.eval x =
      ((Real.gram p x).submatrix choose choose).det := by
  rw [SymmetricAffinePencil.eval_detPolynomial]
  unfold SymmetricAffinePencil.detValue
  rw [principal_matrixAt]

/-- Exact identification with the determinant of the manuscript's rational polynomial submatrix. -/
theorem principal_detPolynomial_eq (p : Real.Parameters) {r : ℕ}
    (choose : Fin r → Fin p.h) :
    (manuscriptPrincipalPencil p choose).detPolynomial =
      Real.realPolynomial (((Real.pencil p).submatrix choose choose).det) := by
  unfold SymmetricAffinePencil.detPolynomial
  have hm : (manuscriptPrincipalPencil p choose).polynomialMatrix =
      ((Real.pencil p).submatrix choose choose).map
        (Polynomial.mapRingHom (Rat.castHom ℝ)) := by
    change ((Real.manuscriptPencil p).polynomialMatrix).submatrix choose choose = _
    rw [Real.manuscriptPencil_polynomialMatrix]
    rfl
  rw [hm]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det
    ((Real.pencil p).submatrix choose choose)).symm

/-- The manuscript's actual rational principal determinant, cast to real coefficients,
has no nonreal complex roots, including when its degree is smaller than its size. -/
theorem rational_principal_roots_real (p : Real.Parameters) (hp : Real.Admissible p)
    {r : ℕ} (choose : Fin r → Fin p.h) (hchoose : Function.Injective choose)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (Real.realPolynomial (((Real.pencil p).submatrix choose choose).det)) = 0) :
    z.im = 0 := by
  apply principal_roots_real p hp choose hchoose z
  rwa [principal_detPolynomial_eq]

end ManuscriptChain.Principal
