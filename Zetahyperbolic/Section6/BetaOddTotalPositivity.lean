import Zetahyperbolic.Section6.BetaOddGram
import Zetahyperbolic.Section3.PositiveMomentMinors

/-!
# Strict total positivity of the actual beta-odd Hankel pencil

All finite orders and arbitrary strictly increasing row/column index selections
are covered. The measure is the constructed beta density, with no unproved
moment-identification or nondegeneracy premise.
-/
noncomputable section
open MeasureTheory Set Matrix

namespace ManuscriptChain.BetaOddGram
open BetaOddMoments

instance momentMeasure_isFiniteMeasure (k N : ℕ) : IsFiniteMeasure (momentMeasure k N) := by
  apply (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1:ℝ) ≠ 0)).mp
  simpa only [pow_zero] using integrable_moment k N 0

theorem momentMeasure_ae_pos (k N : ℕ) : ∀ᵐ t ∂momentMeasure k N, 0 < t := by
  rw [momentMeasure, ae_map_iff (by fun_prop) measurableSet_Ioi]
  have hpos : ∀ᵐ x ∂weightedMeasure k N, x ∈ Ioo 0 1 :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hpos] with x hx
  exact sq_pos_of_pos hx.1

/-- Every mixed minor is strictly positive, for every odd weight and every shift. -/
theorem actual_beta_mixed_minor_pos (k N h : ℕ) {n : ℕ}
    (rows cols : Fin n → Fin h) (hr : StrictMono rows) (hc : StrictMono cols) :
    0 < ((pencil k N h (moment k 0)).submatrix rows cols).det := by
  have h := PositiveMomentMinors.mixed_moment_det_pos (momentMeasure k N)
    (momentMeasure_nonzero k N) (momentMeasure_ae_pos k N)
    (integrable_moment k N) (fun i => (rows i).val) (fun i => (cols i).val) hr hc
  convert h using 1
  congr 1
  ext i j
  rw [integral_moment, even_moment]
  simp only [Matrix.submatrix_apply, pencil, Nat.add_assoc]

end ManuscriptChain.BetaOddGram
