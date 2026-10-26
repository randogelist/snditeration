import Mathlib

/-!
# Andréief's determinant integration identity

The hypotheses are only integrability of the pairwise products. The determinant
integrability and the full factorial identity are proved by finite Leibniz
expansion and Fubini on the product measure, in every finite dimension.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators

namespace ManuscriptChain.MomentAndreief

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
variable (μ : Measure α) [SigmaFinite μ]

def evaluationMatrix (f : ι → α → ℝ) (x : ι → α) : Matrix ι ι ℝ :=
  fun i j => f i (x j)

def pairingMatrix (f g : ι → α → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ t, f i t * g j t ∂μ

theorem det_mul_prod_expansion (f g : ι → α → ℝ) (x : ι → α) :
    (evaluationMatrix f x).det * (∏ i, g i (x i)) =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, (f (σ i) (x i) * g i (x i)) := by
  rw [Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib]
  simp only [evaluationMatrix]
  ring

theorem integrable_det_mul_prod (f g : ι → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    Integrable (fun x : ι → α => (evaluationMatrix f x).det * ∏ i, g i (x i))
      (Measure.pi (fun _ : ι => μ)) := by
  simp_rw [det_mul_prod_expansion]
  apply integrable_finsetSum
  intro σ _
  exact (Integrable.fintype_prod (fun i => hfg (σ i) i)).const_mul _

theorem integral_det_mul_prod (f g : ι → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    (∫ x : ι → α, (evaluationMatrix f x).det * ∏ i, g i (x i)
      ∂Measure.pi (fun _ : ι => μ)) = (pairingMatrix μ f g).det := by
  simp_rw [det_mul_prod_expansion]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_fintype_prod_eq_prod]
    exact (Matrix.det_apply' (pairingMatrix μ f g)).symm
  · intro σ _
    exact (Integrable.fintype_prod (fun i => hfg (σ i) i)).const_mul _

theorem det_mul_det_expansion (f g : ι → α → ℝ) (x : ι → α) :
    (evaluationMatrix f x).det * (evaluationMatrix g x).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ((evaluationMatrix f x).det * ∏ i, g (σ i) (x i)) := by
  rw [Matrix.det_apply' (evaluationMatrix g x), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [evaluationMatrix]
  ring

theorem integrable_det_mul_det (f g : ι → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    Integrable (fun x : ι → α => (evaluationMatrix f x).det *
      (evaluationMatrix g x).det) (Measure.pi (fun _ : ι => μ)) := by
  simp_rw [det_mul_det_expansion]
  apply integrable_finsetSum
  intro σ _
  exact (integrable_det_mul_prod μ f (fun j => g (σ j))
    (fun i j => hfg i (σ j))).const_mul _

/-- The all-order determinant integration identity, with the exact factorial. -/
theorem integral_det_mul_det (f g : ι → α → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t) μ) :
    (∫ x : ι → α, (evaluationMatrix f x).det * (evaluationMatrix g x).det
      ∂Measure.pi (fun _ : ι => μ)) =
      ((Fintype.card ι).factorial : ℝ) * (pairingMatrix μ f g).det := by
  simp_rw [det_mul_det_expansion]
  rw [integral_finsetSum]
  · have he (σ : Equiv.Perm ι) :
        (∫ x : ι → α, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ((evaluationMatrix f x).det * ∏ i, g (σ i) (x i))
          ∂Measure.pi (fun _ : ι => μ)) = (pairingMatrix μ f g).det := by
      rw [integral_const_mul,
        integral_det_mul_prod μ f (fun j => g (σ j)) (fun i j => hfg i (σ j))]
      have hp : pairingMatrix μ f (fun j => g (σ j)) =
          (pairingMatrix μ f g).submatrix id σ := rfl
      rw [hp, Matrix.det_permute', ← mul_assoc]
      have hs : (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ((Equiv.Perm.sign σ : ℤ) : ℝ)) = 1 := by
        exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)
      rw [hs, one_mul]
    simp_rw [he]
    simp [Fintype.card_perm, nsmul_eq_mul]
  · intro σ _
    exact (integrable_det_mul_prod μ f (fun j => g (σ j))
      (fun i j => hfg i (σ j))).const_mul _

end ManuscriptChain.MomentAndreief
