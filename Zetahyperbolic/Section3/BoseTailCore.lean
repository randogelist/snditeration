import Zetahyperbolic.Section3.HyperbolicMomentExp
import Zetahyperbolic.Section3.ZetaTail

/-!
Positive Bose tail integral, part I: geometric expansion and
interchange of sum and exponential moment integral.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem bose_geometric {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, Real.exp (-x * ((n + 1 : ℕ) : ℝ))) =
      1 / (Real.exp x - 1) := by
  have ht (n : ℕ) : Real.exp (-x * ((n + 1 : ℕ) : ℝ)) =
      Real.exp (-x) * Real.exp (-x) ^ n := by
    rw [show -x * ((n + 1 : ℕ) : ℝ) = -x + (n : ℝ) * (-x) by push_cast; ring,
      Real.exp_add, Real.exp_nat_mul]
  simp_rw [ht]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_lt_one_iff.mpr (by linarith))]
  have he : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  have he1 : Real.exp x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
  rw [Real.exp_neg]
  field_simp

def boseTailTerm (k a n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * k) * Real.exp (-((2 * Real.pi / (a : ℝ)) * ((n + a + 1 : ℕ) : ℝ) * t))

def boseTailCoefficient (k a : ℕ) : ℝ :=
  (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi / (a : ℝ)) ^ (2 * k + 1)

theorem boseTailTerm_integrable (k a n : ℕ) (ha : 0 < a) :
    IntegrableOn (boseTailTerm k a n) (Ioi 0) := by
  unfold boseTailTerm
  exact integrableOn_pow_mul_exp _ (by positivity)

theorem integral_boseTailTerm (k a n : ℕ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, boseTailTerm k a n t) =
      boseTailCoefficient k a * (1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1)) := by
  unfold boseTailTerm boseTailCoefficient
  rw [integral_pow_mul_exp _ (by positivity), mul_pow]
  ring

theorem boseTailTerm_nonneg (k a n : ℕ) (t : ℝ) : 0 ≤ boseTailTerm k a n t := by
  unfold boseTailTerm
  exact mul_nonneg (by simpa only [pow_mul] using pow_nonneg (sq_nonneg t) k)
    (Real.exp_nonneg _)

theorem summable_boseTail (k a : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ => 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1)) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff a).mpr (Real.zeta_series_summable (s := 2 * k + 1) (by omega))

theorem summable_integral_norm_boseTailTerm (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    Summable (fun n => ∫ t : ℝ in Ioi 0, ‖boseTailTerm k a n t‖) := by
  simp_rw [Real.norm_of_nonneg (boseTailTerm_nonneg k a _ _), integral_boseTailTerm k a _ ha]
  exact (summable_boseTail k a hk).mul_left _

theorem integral_tsum_boseTailTerm (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ∑' n, boseTailTerm k a n t) =
      boseTailCoefficient k a *
        ∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1) := by
  rw [← integral_tsum_of_summable_integral_norm (fun n => boseTailTerm_integrable k a n ha)
    (summable_integral_norm_boseTailTerm k a hk ha)]
  simp_rw [integral_boseTailTerm k a _ ha]
  rw [tsum_mul_left]

theorem integrableOn_tsum_boseTailTerm (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => ∑' n, boseTailTerm k a n t) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_boseTailTerm k a hk ha]
  apply ne_of_gt
  apply mul_pos
  · unfold boseTailCoefficient
    positivity
  · exact (summable_boseTail k a hk).tsum_pos (fun n => by positivity) 0 (by positivity)

end ManuscriptChain.Hyperbolic
