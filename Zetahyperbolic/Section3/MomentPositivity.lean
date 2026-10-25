import Zetahyperbolic.Section3.ConcretePencil
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Positive moment matrices

For an integrable atomless nonzero measure, a nonzero polynomial has
strictly positive squared integral. This proves Gram positivity from
the actual entrywise moment representation, whenever it is available.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Matrix Polynomial

namespace ManuscriptChain.Moments

def momentMatrix (μ : Measure ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, x ^ (i.val + j.val) ∂μ

theorem eval_ofFn_eq_sum {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n c).eval x = ∑ i, c i * x ^ i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem eval_ofFn_sq_eq_sum {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    ((Polynomial.ofFn n c).eval x) ^ 2 =
      ∑ i, ∑ j, (c i * c j) * x ^ (i.val + j.val) := by
  rw [eval_ofFn_eq_sum, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem integrable_eval_ofFn_sq {μ : Measure ℝ} {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (c : Fin n → ℝ) :
    Integrable (fun x => ((Polynomial.ofFn n c).eval x) ^ 2) μ := by
  simp_rw [eval_ofFn_sq_eq_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (hm i j).const_mul (c i * c j)

theorem quadratic_eq_integral_sq {μ : Measure ℝ} {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (c : Fin n → ℝ) :
    star c ⬝ᵥ (momentMatrix μ n *ᵥ c) =
      ∫ x, ((Polynomial.ofFn n c).eval x) ^ 2 ∂μ := by
  simp_rw [eval_ofFn_sq_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hm i j).const_mul (c i * c j)))]
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hm i j).const_mul (c i * c j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  simp only [momentMatrix]
  ring

theorem integral_polynomial_sq_pos {μ : Measure ℝ} [NullSingletonClass μ]
    (hμ : μ ≠ 0) {q : ℝ[X]} (hq : q ≠ 0)
    (hqi : Integrable (fun x => (q.eval x) ^ 2) μ) :
    0 < ∫ x, (q.eval x) ^ 2 ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (q.eval x)) hqi).2
  have hnull : μ (Function.support (fun x => (q.eval x) ^ 2))ᶜ = 0 := by
    have hset : (Function.support (fun x => (q.eval x) ^ 2))ᶜ =
        {x | Polynomial.IsRoot q x} := by
      ext x
      simp [Function.mem_support, Polynomial.IsRoot]
    rw [hset]
    exact (Polynomial.finite_setOfPred_isRoot hq).measure_zero μ
  rw [measure_of_measure_compl_eq_zero hnull]
  exact Measure.measure_univ_pos.mpr hμ

theorem momentMatrix_posDef {μ : Measure ℝ} [NullSingletonClass μ]
    (hμ : μ ≠ 0) {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ) :
    (momentMatrix μ n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [momentMatrix, Nat.add_comm]
  · intro c hc
    rw [quadratic_eq_integral_sq hm c]
    apply integral_polynomial_sq_pos hμ _ (integrable_eval_ofFn_sq hm c)
    intro h
    apply hc
    apply Polynomial.injective_ofFn n
    simpa using h

end ManuscriptChain.Moments
