import Zetahyperbolic.Section3.PoleScalingIntegral
import Zetahyperbolic.Section3.CothFormula
import Zetahyperbolic.Section3.BoseTailFormula

/-!
Algebraic combination of the cotangent resolvent kernel
and the Gamma/Bose integrals, for the actual simple-pole value.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem pole_scaled_kernel_split_algebra (k : ℕ) (hk : 0 < k)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t)) *
        (Real.pi / (a * t) * (1 / 2 + 1 / (Real.exp (2 * Real.pi * t / a) - 1)) -
          1 / (2 * t ^ 2)) =
      (Real.pi / a) *
        (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
          (Real.exp (2 * Real.pi * t / a) - 1)) +
      (Real.pi / (2 * a)) * (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t))) -
      (1 / 2) * (t ^ (2 * k - 1) * Real.exp (-(2 * Real.pi * t))) := by
  have he : Real.exp (2 * Real.pi * t / a) - 1 ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hpow2 : t ^ (2 * k) = t ^ (2 * k - 1) * t := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow3 : t ^ (2 * k + 1) = t ^ (2 * k - 1) * t ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow3, hpow2]
  field_simp
  ring

theorem pole_integral_constants (k a : ℕ) (hk : 0 < k) (ha : 0 < a) (tail : ℝ) :
    (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
      ((Real.pi / (a : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
          (a : ℝ) ^ (2 * k + 1) * tail) +
       (Real.pi / (2 * (a : ℝ))) *
         ((Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1)) -
       (1 / 2) *
         ((Nat.factorial (2 * k - 1) : ℝ) / (2 * Real.pi) ^ (2 * k))) =
      (a : ℝ) ^ (2 * k) * tail + 1 / (2 * (a : ℝ)) - 1 / (2 * (k : ℝ)) := by
  have hf : (Nat.factorial (2 * k) : ℝ) =
      (2 * (k : ℝ)) * (Nat.factorial (2 * k - 1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (show 2 * k ≠ 0 by omega)).symm
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hp0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hf0 : (Nat.factorial (2 * k - 1) : ℝ) ≠ 0 := by positivity
  rw [hf, pow_succ (2 * Real.pi), pow_succ (a : ℝ)]
  field_simp

end ManuscriptChain.Hyperbolic
