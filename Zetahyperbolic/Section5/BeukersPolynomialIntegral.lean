import Zetahyperbolic.Section5.KreinPolynomial

/-!
# Actual finite-polynomial Beukers integral

The prior coefficient form was defined as a finite sum of actual moments.
Here every mixed moment is proved integrable, so finite linearity identifies
that form with the literal product-polynomial integral against the same density.
No arbitrary-L² completion or definite-cone assertion is made.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.Beukers

/-- Every mixed monomial of the actual Beukers density is integrable. -/
theorem density_monomial_integrable (r t : ℕ) :
    Integrable (fun z : ℝ × ℝ => z.1 ^ r * z.2 ^ t * density z) squareMeasure := by
  have hs : Summable (fun n => ∫ z, momentTerm r t n z ∂squareMeasure) := by
    simpa only [integral_norm_momentTerm] using summable_integral_norm_momentTerm r t
  have hn (n : ℕ) : 0 ≤ ∫ z, momentTerm r t n z ∂squareMeasure := by
    rw [integral_momentTerm]
    positivity
  have hp : 0 < ∫ z, momentTerm r t 0 z ∂squareMeasure := by
    rw [integral_momentTerm]
    apply mul_pos (by norm_num)
    apply Finset.sum_pos
    · intro j _
      positivity
    · exact Finset.univ_nonempty
  have he : (∫ z, z.1 ^ r * z.2 ^ t * density z ∂squareMeasure) =
      ∑' n, ∫ z, momentTerm r t n z ∂squareMeasure := by
    rw [integral_density_moment_series]
    apply tsum_congr
    intro n
    exact (integral_momentTerm r t n).symm
  apply Integrable.of_integral_ne_zero
  rw [he]
  exact ne_of_gt (hp.trans_le (hs.le_tsum 0 (fun n _ => hn n)))

/-- A rational coefficient vector evaluated as the literal finite polynomial. -/
def coefficientPolynomialValue {K : ℕ} (c : Fin (K + 1) → ℚ) (x : ℝ) : ℝ :=
  ∑ r : Fin (K + 1), (c r : ℝ) * x ^ r.val

private theorem polynomial_product_expansion {K : ℕ}
    (c d : Fin (K + 1) → ℚ) (z : ℝ × ℝ) :
    coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 * density z =
      ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
        (c r : ℝ) * (d t : ℝ) * (z.1 ^ r.val * z.2 ^ t.val * density z) := by
  simp only [coefficientPolynomialValue, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The actual finite polynomial product is integrable, with no sign constraint
on either rational coefficient vector. -/
theorem polynomial_product_integrable {K : ℕ} (c d : Fin (K + 1) → ℚ) :
    Integrable (fun z : ℝ × ℝ =>
      coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 * density z)
      squareMeasure := by
  simp_rw [polynomial_product_expansion]
  apply integrable_finset_sum
  intro r _
  apply integrable_finset_sum
  intro t _
  exact (density_monomial_integrable r.val t.val).const_mul _

/-- The coefficient pairing is exactly the original unit-square product integral,
not merely a formal bilinear extension of a list of moments. -/
theorem integral_polynomial_product_eq_momentForm {K : ℕ}
    (c d : Fin (K + 1) → ℚ) :
    (∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 *
      density z ∂squareMeasure) = polynomialMomentForm c d := by
  simp_rw [polynomial_product_expansion]
  rw [integral_finset_sum]
  · unfold polynomialMomentForm
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul]
    · intro t _
      exact (density_monomial_integrable r.val t.val).const_mul _
  · intro r _
    apply integrable_finset_sum
    intro t _
    exact (density_monomial_integrable r.val t.val).const_mul _

/-- Actual product-integral version of the finite-polynomial Krein identity. -/
theorem integral_polynomial_product_eq_krein {K : ℕ}
    (c d : Fin (K + 1) → ℚ) :
    (∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 *
      density z ∂squareMeasure) =
      ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
        (c r : ℝ) * (d t : ℝ) *
          (∑' m : ℕ,
            kreinSignedPairing (kreinChannel r.val m) (kreinChannel t.val m)) := by
  rw [integral_polynomial_product_eq_momentForm, polynomialMomentForm_eq_krein]

end ManuscriptChain.Beukers
