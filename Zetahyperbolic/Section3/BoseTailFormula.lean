import Zetahyperbolic.Section3.BoseTailCore

/-!
Positive Bose tail integral, part II: identifies its value with
the exact shifted odd-zeta Dirichlet series.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem bose_tail_eq_tsum (k a : ℕ) (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1) =
        ∑' n, boseTailTerm k a n t := by
  have ha' : (a : ℝ) ≠ 0 := by positivity
  rw [div_eq_mul_inv, ← one_div, ← bose_geometric (by positivity)]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold boseTailTerm
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  field_simp
  ring

theorem integrableOn_bose_tail (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) (Ioi 0) := by
  exact (integrableOn_tsum_boseTailTerm k a hk ha).congr_fun
    (fun t ht => (bose_tail_eq_tsum k a ha ht).symm) measurableSet_Ioi

theorem integral_bose_tail_tsum (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) =
        (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
          (a : ℝ) ^ (2 * k + 1) *
            ∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => bose_tail_eq_tsum k a ha ht),
    integral_tsum_boseTailTerm k a hk ha]
  unfold boseTailCoefficient
  rw [div_pow]
  congr 1
  field_simp

theorem integral_bose_tail (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) =
        (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
          (a : ℝ) ^ (2 * k + 1) *
            (Real.zeta (2 * k + 1) - (Real.harmonic (2 * k + 1) a : ℝ)) := by
  rw [integral_bose_tail_tsum k a hk ha]
  have htail : (∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1)) =
      Real.zeta (2 * k + 1) - (Real.harmonic (2 * k + 1) a : ℝ) := by
    simpa only [Nat.add_comm a] using Real.zeta_tail_sum (s := 2 * k + 1) (by omega) a
  rw [htail]

end ManuscriptChain.Hyperbolic
