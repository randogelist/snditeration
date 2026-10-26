import Zetahyperbolic.Section3.ShiftedMomentPositivity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square-root coordinates for the concrete moment measure

On a measure supported almost everywhere on the nonnegative half-line,
pushing forward by square root preserves the original moments as even
moments. Squaring the resulting measure recovers the original measure.

These coordinate identities and the finite-mass instance are prerequisites
for a symmetric-square-root proof of Stieltjes determinacy. They do not
assert determinacy, exponential integrability, or equality of competing
measures.
-/

noncomputable section
open MeasureTheory

namespace ManuscriptChain.MomentSquareRoot

/-- Squaring the square-root pushforward recovers a nonnegative-support
measure. The support condition is only required almost everywhere. -/
theorem map_sq_map_sqrt (μ : Measure ℝ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) :
    (μ.map _root_.Real.sqrt).map (fun y : ℝ => y ^ 2) = μ := by
  rw [Measure.map_map (by fun_prop) _root_.Real.continuous_sqrt.measurable]
  calc
    μ.map ((fun y : ℝ => y ^ 2) ∘ _root_.Real.sqrt) = μ.map id := by
      apply Measure.map_congr
      filter_upwards [hμ] with t ht
      exact _root_.Real.sq_sqrt ht
    _ = μ := Measure.map_id

/-- Integer moments become even moments under the positive square-root
pushforward. No integrability premise is needed for this integral identity. -/
theorem integral_even_map_sqrt (μ : Measure ℝ)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ) :
    (∫ y : ℝ, y ^ (2 * n) ∂μ.map _root_.Real.sqrt) =
      ∫ t : ℝ, t ^ n ∂μ := by
  rw [integral_map _root_.Real.continuous_sqrt.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [hμ] with t ht
  rw [pow_mul, _root_.Real.sq_sqrt ht]

end ManuscriptChain.MomentSquareRoot

namespace ManuscriptChain.ConcreteMoment

/-- Integrability of the zeroth actual moment gives finite total mass. -/
instance momentMeasure_isFiniteMeasure (p : Real.Parameters) :
    IsFiniteMeasure (momentMeasure p) := by
  apply (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
  simpa only [pow_zero] using integrable_moment p 0

/-- The positive square-root coordinate loses no measure information. -/
theorem momentMeasure_map_sq_map_sqrt (p : Real.Parameters) :
    ((momentMeasure p).map _root_.Real.sqrt).map (fun y : ℝ => y ^ 2) =
      momentMeasure p := by
  apply MomentSquareRoot.map_sq_map_sqrt
  filter_upwards [momentMeasure_ae_pos p] with t ht
  exact ht.le

/-- Every original actual moment is an even moment of its square-root
pushforward. -/
theorem integral_even_sqrt_momentMeasure (p : Real.Parameters) (n : ℕ) :
    (∫ y : ℝ, y ^ (2 * n) ∂(momentMeasure p).map _root_.Real.sqrt) =
      ∫ t : ℝ, t ^ n ∂momentMeasure p := by
  apply MomentSquareRoot.integral_even_map_sqrt
  filter_upwards [momentMeasure_ae_pos p] with t ht
  exact ht.le

end ManuscriptChain.ConcreteMoment
