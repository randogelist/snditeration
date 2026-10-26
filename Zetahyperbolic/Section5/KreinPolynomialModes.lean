import Zetahyperbolic.Section5.BeukersPolynomialIntegral

/-!
# Actual polynomial Mellin channels and convergent Krein series

This is the finite-polynomial stage of Theorem 5.2(2). It identifies each
channel with its actual integral and proves the finite/infinite interchange.
The arbitrary-L² extension and positive/negative cone existence are not asserted.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.Beukers

/-- The actual finite polynomial's Mellin-log channel. -/
def polynomialKreinChannel {K : ℕ} (c : Fin (K + 1) → ℚ) (m ν : ℕ) : ℝ :=
  ∑ r : Fin (K + 1), (c r : ℝ) * kreinChannel r.val m ν

/-- Integral identification of every channel, with the same factorial convention
as the already proved monomial Krein formula. -/
theorem polynomialKreinChannel_eq_integral {K : ℕ}
    (c : Fin (K + 1) → ℚ) (m ν : ℕ) :
    polynomialKreinChannel c m ν =
      ∫ x : ℝ in Ioo 0 1,
        coefficientPolynomialValue c x * x ^ m * (-_root_.Real.log x) ^ ν := by
  have hexpand : (fun x : ℝ =>
      coefficientPolynomialValue c x * x ^ m * (-_root_.Real.log x) ^ ν) =
      (fun x => ∑ r : Fin (K + 1),
        (c r : ℝ) * (x ^ (r.val + m) * (-_root_.Real.log x) ^ ν)) := by
    funext x
    simp only [coefficientPolynomialValue, Finset.sum_mul, pow_add]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hexpand, integral_finset_sum]
  · unfold polynomialKreinChannel
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_const_mul, UnitLogMoments.integral_pow_log]
    rfl
  · intro r _
    exact (UnitLogMoments.integrable_pow_log (r.val + m) ν).const_mul _

private theorem kreinSix_sum_left {ι : Type*} [Fintype ι]
    (a : ι → ℕ → ℝ) (b : ℕ → ℝ) :
    kreinSixPairing (fun ν => ∑ i, a i ν) b = ∑ i, kreinSixPairing (a i) b := by
  classical
  unfold kreinSixPairing
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem kreinSix_sum_right {ι : Type*} [Fintype ι]
    (a : ℕ → ℝ) (b : ι → ℕ → ℝ) :
    kreinSixPairing a (fun ν => ∑ i, b i ν) = ∑ i, kreinSixPairing a (b i) := by
  classical
  unfold kreinSixPairing
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem kreinSix_scale (a b : ℕ → ℝ) (c d : ℝ) :
    kreinSixPairing (fun ν => c * a ν) (fun ν => d * b ν) =
      c * d * kreinSixPairing a b := by
  unfold kreinSixPairing
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- Pairing of the actual polynomial channels is the finite bilinear expansion
of the original monomial pairings, with no positivity assumption. -/
theorem polynomial_channel_pairing_expansion {K : ℕ}
    (c d : Fin (K + 1) → ℚ) (m : ℕ) :
    kreinSignedPairing (polynomialKreinChannel c m) (polynomialKreinChannel d m) =
      ∑ r : Fin (K + 1), ∑ t : Fin (K + 1),
        (c r : ℝ) * (d t : ℝ) *
          kreinSignedPairing (kreinChannel r.val m) (kreinChannel t.val m) := by
  simp_rw [← kreinSix_eq_signed]
  unfold polynomialKreinChannel
  rw [kreinSix_sum_left]
  apply Finset.sum_congr rfl
  intro r _
  rw [kreinSix_sum_right]
  apply Finset.sum_congr rfl
  intro t _
  exact kreinSix_scale _ _ _ _

/-- The paired monomial modes form a summable real series. -/
theorem summable_monomial_krein_pairing (r t : ℕ) :
    Summable (fun m => kreinSignedPairing (kreinChannel r m) (kreinChannel t m)) := by
  have hs : Summable (fun m => ∫ z, momentTerm r t m z ∂squareMeasure) := by
    simpa only [integral_norm_momentTerm] using summable_integral_norm_momentTerm r t
  simpa only [integral_momentTerm_eq_kreinSix, kreinSix_eq_signed] using hs

/-- Every finite polynomial has a convergent paired signed-mode expansion.
The value is the actual product integral, not a formal rearrangement. -/
theorem hasSum_polynomial_krein_pairing {K : ℕ} (c d : Fin (K + 1) → ℚ) :
    HasSum
      (fun m => kreinSignedPairing (polynomialKreinChannel c m) (polynomialKreinChannel d m))
      (∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 *
        density z ∂squareMeasure) := by
  rw [integral_polynomial_product_eq_krein]
  simp_rw [polynomial_channel_pairing_expansion]
  apply hasSum_sum
  intro r _
  apply hasSum_sum
  intro t _
  exact (summable_monomial_krein_pairing r.val t.val).hasSum.mul_left
    ((c r : ℝ) * (d t : ℝ))

/-- Single-tsum version of the literal product-polynomial Krein integral. -/
theorem integral_polynomial_product_eq_channel_tsum {K : ℕ}
    (c d : Fin (K + 1) → ℚ) :
    (∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue d z.2 *
      density z ∂squareMeasure) =
      ∑' m, kreinSignedPairing (polynomialKreinChannel c m) (polynomialKreinChannel d m) :=
  (hasSum_polynomial_krein_pairing c d).tsum_eq.symm

end ManuscriptChain.Beukers
