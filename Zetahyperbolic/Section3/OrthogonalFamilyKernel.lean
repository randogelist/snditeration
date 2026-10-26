import Zetahyperbolic.Section3.PrintedMomentMeasure

/-!
# The kernel for any supplied monic orthogonal family

Theorem 3.8 allows a supplied monic orthogonal family. This file proves that
its integral-normalized kernel is the inverse-Gram kernel, without assuming
that the supplied family is the canonical LDL construction.
-/
noncomputable section
open scoped BigOperators
open Matrix Polynomial MeasureTheory

namespace ManuscriptChain.OrthogonalFamilyKernel

variable {n : ℕ}

theorem ofFn_coeff_eq (q : ℝ[X]) (hq : q.natDegree < n) :
    Polynomial.ofFn n (fun i : Fin n => q.coeff i.val) = q := by
  ext j
  by_cases hj : j < n
  · simp only [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj)]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hq (Nat.le_of_not_gt hj))).symm

theorem congruence_entry_eq_pairing (C G : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (C * G * C.transpose) i j = C i ⬝ᵥ (G *ᵥ C j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem inverse_of_diagonal_congruence (C G : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hC : IsUnit C.det)
    (hcong : C * G * C.transpose = Matrix.diagonal d) (hd : ∀ i, d i ≠ 0) :
    G⁻¹ = C.transpose * Matrix.diagonal (fun i => (d i)⁻¹) * C := by
  have hD : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hd i]
    · simp [hij]
  have hCT : IsUnit C.transpose.det := by
    simpa only [Matrix.det_transpose] using hC
  have hi := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) hcong
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD] at hi
  have hh := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => C.transpose * A * C) hi
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hCT,
    Matrix.nonsing_inv_mul_cancel_right _ _ hC] at hh
  exact hh

/-- Every supplied monic degree-indexed orthogonal family has the same kernel.
Its squared norms are nonzero consequences of the hypotheses, not additional inputs. -/
theorem kernel_eq_inverseGram {μ : Measure ℝ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x^(i.val+j.val)) μ)
    (hG : ∀ i j, G i j = ∫ x, x^(i.val+j.val) ∂μ) (hpos : G.PosDef)
    (q : Fin n → ℝ[X]) (hmonic : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = i.val)
    (horthog : ∀ i j, i ≠ j → (∫ x, (q i).eval x * (q j).eval x ∂μ) = 0)
    (t u : ℝ) :
    (∑ i, (q i).eval t * (q i).eval u / (∫ x, ((q i).eval x)^2 ∂μ)) =
      (fun i : Fin n => t^i.val) ⬝ᵥ (G⁻¹ *ᵥ (fun i : Fin n => u^i.val)) := by
  let C : Matrix (Fin n) (Fin n) ℝ := fun i j => (q i).coeff j.val
  let d : Fin n → ℝ := fun i => ∫ x, ((q i).eval x)^2 ∂μ
  have hpoly (i : Fin n) : Polynomial.ofFn n (C i) = q i := by
    apply ofFn_coeff_eq
    rw [hdegree i]
    exact i.isLt
  have hdiag (i : Fin n) : C i i = 1 := by
    change (q i).coeff i.val = 1
    rw [← hdegree i]
    exact (hmonic i).coeff_natDegree
  have htri (i j : Fin n) (hij : i < j) : C i j = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [hdegree i]
    exact hij
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular C (fun i j hij => htri i j hij)]
    simp only [hdiag, Finset.prod_const_one]
  have hC : IsUnit C.det := by rw [hdet]; exact isUnit_one
  have hpair (i j : Fin n) :
      C i ⬝ᵥ (G *ᵥ C j) = ∫ x, (q i).eval x * (q j).eval x ∂μ := by
    simpa only [hpoly] using
      ChristoffelDarboux.bilinear_eq_integral_product hm hG (C i) (C j)
  have hd (i : Fin n) : 0 < d i := by
    have hrow : C i ≠ 0 := by
      intro hz
      have hi := congrFun hz i
      rw [hdiag] at hi
      exact one_ne_zero hi
    dsimp only [d]
    simp_rw [pow_two]
    rw [← hpair i i]
    simpa only [star_trivial] using hpos.dotProduct_mulVec_pos hrow
  have hcong : C * G * C.transpose = Matrix.diagonal d := by
    ext i j
    rw [congruence_entry_eq_pairing, hpair]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, d, pow_two]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact horthog i j hij
  have heval (i : Fin n) (x : ℝ) : (q i).eval x = ∑ j, C i j * x^j.val := by
    rw [← hpoly i, Moments.eval_ofFn_eq_sum]
  rw [inverse_of_diagonal_congruence C G d hC hcong (fun i => ne_of_gt (hd i)),
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct]
  simp only [Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [heval i t, heval i u]
  change (∑ j, C i j * t^j.val) * (∑ j, C i j * u^j.val) / d i = _
  simp only [div_eq_mul_inv, mul_comm]
  ring

/-- The arbitrary supplied family in the printed Theorem 3.8 has exactly the
same kernel as the canonical family, for the literal printed measure. -/
theorem actual_kernel_eq_canonical (p : Real.Parameters) (hp : Real.Admissible p)
    (q : Fin p.h → ℝ[X]) (hmonic : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = i.val)
    (horthog : ∀ i j, i ≠ j → (∫ x, (q i).eval x * (q j).eval x
      ∂PrintedMomentMeasure.printedMeasure p 1) = 0) (t u : ℝ) :
    (∑ i, (q i).eval t * (q i).eval u / (∫ x, ((q i).eval x)^2
      ∂PrintedMomentMeasure.printedMeasure p 1)) =
      ChristoffelDarboux.actualKernel p hp t u := by
  rw [ChristoffelDarboux.actualKernel_inverseGram]
  have hm := (REALIZATION p hp).integrable_moments
  have hG := (REALIZATION p hp).moment_identity
  rw [PrintedMomentMeasure.realizationMeasure_eq_printed p hp] at hm hG
  exact kernel_eq_inverseGram hm hG (GRAM_POSITIVE p hp) q hmonic hdegree horthog t u

/-- The same supplied-family quantifier closure applies to every positive
Laplace parameter appearing in the derivative clause. -/
theorem laplace_kernel_eq_canonical (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ)
    (q : Fin p.h → ℝ[X]) (hmonic : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = i.val)
    (horthog : ∀ i j, i ≠ j → (∫ x, (q i).eval x * (q j).eval x
      ∂PrintedMomentMeasure.printedMeasure p τ) = 0) (t u : ℝ) :
    (∑ i, (q i).eval t * (q i).eval u / (∫ x, ((q i).eval x)^2
      ∂PrintedMomentMeasure.printedMeasure p τ)) =
      ChristoffelDarboux.kernel (LaplaceGramMeasure.gram_positive p hτ) t u := by
  rw [ChristoffelDarboux.kernel_eq_inverseGram]
  have hm (i j : Fin p.h) := LaplaceGramMeasure.integrable_momentMeasure p (i.val+j.val) hτ
  have hG (i j : Fin p.h) := (LaplaceGramMeasure.integral_momentMeasure p (i.val+j.val) hτ).symm
  rw [PrintedMomentMeasure.momentMeasure_eq_printed] at hm hG
  exact kernel_eq_inverseGram hm hG (LaplaceGramMeasure.gram_positive p hτ)
    q hmonic hdegree horthog t u

/-- The pole-spectrum clause with the supplied family, rather than a chosen
construction, in every entry of the pole matrix. -/
theorem actual_supplied_family_charpoly (p : Real.Parameters) (hp : Real.Admissible p)
    (q : Fin p.h → ℝ[X]) (hmonic : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = i.val)
    (horthog : ∀ i j, i ≠ j → (∫ x, (q i).eval x * (q j).eval x
      ∂PrintedMomentMeasure.printedMeasure p 1) = 0) :
    (Spectral.whitenedMatrix (Real.manuscriptPencil p)).charpoly =
      (fun a b : Fin p.h => (PoleDiagonalization.poleWeight p a : ℝ) *
        ∑ i, (q i).eval (ChristoffelDarboux.actualPoleNode p a) *
          (q i).eval (ChristoffelDarboux.actualPoleNode p b) /
          (∫ x, ((q i).eval x)^2 ∂PrintedMomentMeasure.printedMeasure p 1)).charpoly := by
  rw [ChristoffelDarboux.actual_whitened_charpoly_eq_pole p hp]
  congr 1
  ext a b
  dsimp only [ChristoffelDarboux.actualPoleOperator]
  rw [actual_kernel_eq_canonical p hp q hmonic hdegree horthog]

/-- The derivative clause with any supplied monic orthogonal family at the
given positive Laplace parameter. -/
theorem laplace_supplied_family_deriv (p : Real.Parameters) {τ : ℝ} (hτ : 0 < τ)
    (q : Fin p.h → ℝ[X]) (hmonic : ∀ i, (q i).Monic)
    (hdegree : ∀ i, (q i).natDegree = i.val)
    (horthog : ∀ i j, i ≠ j → (∫ x, (q i).eval x * (q j).eval x
      ∂PrintedMomentMeasure.printedMeasure p τ) = 0) :
    deriv (fun z => Real.log ((LaplaceGramMeasure.gram p z).det)) τ =
      ∫ y in Set.Ioi (0 : ℝ),
        (∑ i, (q i).eval (y^2) * (q i).eval (y^2) /
          (∫ x, ((q i).eval x)^2 ∂PrintedMomentMeasure.printedMeasure p τ)) *
        LaplaceMomentDerivative.weight p y *
        deriv (fun z => LaplaceWeightDerivative.density p.k z y) τ := by
  rw [PrintedMomentMeasure.laplace_logDet_deriv p hτ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  rw [laplace_kernel_eq_canonical p hτ q hmonic hdegree horthog]

end ManuscriptChain.OrthogonalFamilyKernel
