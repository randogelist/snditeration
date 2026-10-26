import Zetahyperbolic.Section3.RootZeros
import Mathlib

/-!
# Hermitian spectral construction for Theorem 3.1

Constructs, rather than assumes, a complete spectral factorization from
positive definiteness of the Gram matrix and nonsingularity of the slope.
The actual manuscript Gram positivity remains a separate analytic endpoint.
-/

noncomputable section
open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace ManuscriptChain.Spectral

theorem det_one_add_smul_of_hermitian {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (t : ℝ) :
    Matrix.det (1 + t • B) = ∏ i, (1 + t * hB.eigenvalues i) := by
  let e := Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary
  have he : B = e (diagonal hB.eigenvalues) := by
    simpa [e, Function.comp_def] using hB.spectral_theorem
  have hmap : 1 + t • B = e (1 + t • diagonal hB.eigenvalues) := by
    simp only [map_add, map_one, map_smul, ← he]
  rw [hmap]
  change Matrix.det (e (1 + t • diagonal hB.eigenvalues)) = _
  dsimp only [e]
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm, ← Matrix.mul_assoc]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
  have hd : (1 : Matrix (Fin n) (Fin n) ℝ) + t • diagonal hB.eigenvalues =
      diagonal (fun i => 1 + t * hB.eigenvalues i) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [hd, Matrix.det_diagonal]

theorem rootFactorization_nonempty_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) :
    Nonempty (RootFactorization p) := by
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
  have hSinvdet : Matrix.det (S⁻¹) ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det S hSunit).ne_zero
  let B := S⁻¹ * p.direction * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.direction_symmetric)
    simpa only [hSsymm.inv.eq] using h
  have hBdet : Matrix.det B ≠ 0 := by
    dsimp only [B]
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hSinvdet direction_nonzero) hSinvdet
  have hconj : S * B * S = p.direction := by
    dsimp only [B]
    calc
      S * (S⁻¹ * p.direction * S⁻¹) * S =
          (S * S⁻¹) * p.direction * (S⁻¹ * S) := by
            simp only [Matrix.mul_assoc]
      _ = p.direction := by
        rw [Matrix.mul_nonsing_inv S hSunit, Matrix.nonsing_inv_mul S hSunit]
        simp
  have hpencil (x : ℝ) : p.matrixAt x = S * (1 + (x - p.center) • B) * S := by
    calc
      p.matrixAt x = S * S + (x - p.center) • (S * B * S) := by
        rw [hSsq, hconj]
        rfl
      _ = S * (1 + (x - p.center) • B) * S := by
        simp [Matrix.mul_add, Matrix.add_mul]
  refine ⟨{
    beta := hBsymm.eigenvalues
    beta_ne_zero := ?_
    base_det_ne_zero := hbase
    factorization := ?_
  }⟩
  · intro i hi
    apply hBdet
    rw [hBsymm.det_eq_prod_eigenvalues]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi
  · apply Polynomial.funext
    intro x
    rw [p.eval_detPolynomial, SymmetricAffinePencil.detValue, hpencil]
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetbase : Matrix.det S * Matrix.det S = Matrix.det p.base := by
      rw [← Matrix.det_mul, hSsq]
    rw [det_one_add_smul_of_hermitian B hBsymm]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      eval_spectralFactor]
    calc
      Matrix.det S * (∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i)) *
          Matrix.det S = (Matrix.det S * Matrix.det S) *
            ∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i) := by ring
      _ = _ := by rw [hdetbase]

noncomputable def rootFactorizationOfPosDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) : RootFactorization p :=
  Classical.choice (rootFactorization_nonempty_of_posDef p positive direction_nonzero)

theorem theorem_3_1_degree_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) :
    p.detPolynomial.natDegree = n :=
  (rootFactorizationOfPosDef p positive direction_nonzero).natDegree_eq

theorem theorem_3_1_hyperbolicity_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 :=
  (rootFactorizationOfPosDef p positive direction_nonzero).complex_root_im_zero z hz

end ManuscriptChain.Spectral
