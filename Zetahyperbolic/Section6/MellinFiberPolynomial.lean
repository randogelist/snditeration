import Zetahyperbolic.Section6.MellinFiberWeighted
import Zetahyperbolic.Section5.BeukersIntegralPencil

/-! The multiplicative-fiber identity for the actual weighted measure and
arbitrary rational polynomials, with exactly the manuscript's degree cutoff. -/
noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace ManuscriptChain.Beukers.Mellin

def polynomialFiber (A B : ℚ[X]) (u : ℝ) : ℝ :=
  ∫ y : ℝ in Ioo 0 1,
    A.eval₂ (Rat.castHom ℝ) (u^y) * B.eval₂ (Rat.castHom ℝ) (u^(1-y))

lemma coefficient_value_eq_eval {K : ℕ} (A : ℚ[X]) (hA : A.natDegree ≤ K) (x : ℝ) :
    coefficientPolynomialValue (fun r : Fin (K+1) => A.coeff r.val) x =
      A.eval₂ (Rat.castHom ℝ) x := by
  rw [Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (Nat.lt_succ_of_le hA) x]
  simp only [coefficientPolynomialValue, Rat.coe_castHom]
  exact Fin.sum_univ_eq_sum_range (fun n => (A.coeff n : ℝ) * x^n) (K+1)

theorem polynomialFiber_eq_sum {K : ℕ} (A B : ℚ[X])
    (hA : A.natDegree ≤ K) (hB : B.natDegree ≤ K) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    polynomialFiber A B u = ∑ r : Fin (K+1), ∑ t : Fin (K+1),
      (A.coeff r.val : ℝ) * (B.coeff t.val : ℝ) * fiberMonomial r.val t.val u := by
  simpa only [fiber, coefficient_value_eq_eval A hA, coefficient_value_eq_eval B hB,
    polynomialFiber] using
    fiber_eq_sum (fun r : Fin (K+1) => A.coeff r.val)
      (fun t : Fin (K+1) => B.coeff t.val) hu

theorem polynomialFiber_weight_integrable {K : ℕ} (A B : ℚ[X])
    (hA : A.natDegree ≤ K) (hB : B.natDegree ≤ K) :
    IntegrableOn (fun u => polynomialFiber A B u * mellinWeight u) (Ioo 0 1) := by
  simpa only [fiber, coefficient_value_eq_eval A hA, coefficient_value_eq_eval B hB,
    polynomialFiber] using
    integrable_fiber_polynomial_weight (fun r : Fin (K+1) => A.coeff r.val)
      (fun t : Fin (K+1) => B.coeff t.val)

/-- The exact 6.1(1) Mellin identity for the measure of Theorem 5.1. -/
theorem theorem_6_1_mellin_identity {K : ℕ} (A B : ℚ[X])
    (hA : A.natDegree ≤ K) (hB : B.natDegree ≤ K) :
    (∫ z, A.eval₂ (Rat.castHom ℝ) z.1 * B.eval₂ (Rat.castHom ℝ) z.2
      ∂beukersMeasure) =
        ∫ u : ℝ in Ioo 0 1, polynomialFiber A B u * mellinWeight u := by
  rw [integral_beukersMeasure]
  simpa only [fiber, coefficient_value_eq_eval A hA, coefficient_value_eq_eval B hB,
    polynomialFiber] using
    polynomial_mellin_fiber_reduction (fun r : Fin (K+1) => A.coeff r.val)
      (fun t : Fin (K+1) => B.coeff t.val)

end ManuscriptChain.Beukers.Mellin
