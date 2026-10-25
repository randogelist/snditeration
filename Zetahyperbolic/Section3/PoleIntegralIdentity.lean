import Zetahyperbolic.Section3.PoleKernelAlgebra

/-!
The exact simple-pole integral formula (2.3), now assembled
without an analytic assumption from cotangent partial fractions,
positive measure changes of variables, and Gamma/Bose integrals.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

def PoleIntegralIdentity (k : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a →
    (∫ y : ℝ in Ioi 0, density k y / (y ^ 2 + (a : ℝ) ^ 2)) =
      (a : ℝ) ^ (2 * k) * Real.zeta (2 * k + 1) +
        (Real.poleConstant k a : ℝ)

theorem poleIntegralIdentity (k : ℕ) (hk : 0 < k) : PoleIntegralIdentity k := by
  intro a ha
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < 2 * Real.pi := by positivity
  have hBint : IntegrableOn
      (fun t : ℝ => t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
        (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_bose_tail k a hk ha
  have hGint := integrableOn_pow_mul_exp (2 * k) hbR
  have hHint := integrableOn_pow_mul_exp (2 * k - 1) hbR
  have hB : (∫ t : ℝ in Ioi 0,
      t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
        (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) =
      (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
        (a : ℝ) ^ (2 * k + 1) *
          (Real.zeta (2 * k + 1) - (Real.harmonic (2 * k + 1) a : ℝ)) := by
    simpa only [neg_mul] using integral_bose_tail k a hk ha
  have hsplit :
      (∫ t : ℝ in Ioi 0, t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t)) *
        (∑' n : ℕ, 1 / (t ^ 2 + ((a : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2))) =
      (Real.pi / (a : ℝ)) *
        (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
          (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) +
      (Real.pi / (2 * (a : ℝ))) *
        (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi * t))) -
      (1 / 2) *
        (∫ t : ℝ in Ioi 0, t ^ (2 * k - 1) * Real.exp (-(2 * Real.pi * t))) := by
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (Real.pi / (a : ℝ)) *
            (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
              (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) +
          (Real.pi / (2 * (a : ℝ))) *
            (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t))) -
          (1 / 2) *
            (t ^ (2 * k - 1) * Real.exp (-(2 * Real.pi * t))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [coth_partial_fractions ht haR]
        exact pole_scaled_kernel_split_algebra k hk haR ht
      _ = _ := by
        have hBmul := hBint.const_mul (Real.pi / (a : ℝ))
        have hGmul := hGint.const_mul (Real.pi / (2 * (a : ℝ)))
        have hHmul := hHint.const_mul (1 / 2 : ℝ)
        have hs0 := integral_sub (hBmul.add hGmul) hHmul
        have hs1 := integral_add hBmul hGmul
        simp only [Pi.add_apply] at hs0 hs1
        rw [hs0, hs1]
        simp only [integral_const_mul]
  rw [integral_density_div_quadratic k haR, hsplit, hB,
    integral_pow_mul_exp (2 * k) hbR,
    integral_pow_mul_exp (2 * k - 1) hbR,
    show 2 * k - 1 + 1 = 2 * k by omega,
    pole_integral_constants k a hk ha]
  unfold Real.poleConstant
  push_cast
  ring

end ManuscriptChain.Hyperbolic
