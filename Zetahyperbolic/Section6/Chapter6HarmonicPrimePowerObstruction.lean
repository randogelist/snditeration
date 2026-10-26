import Zetahyperbolic.Section5.BetaBeukersMoments
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The missing prime-size restriction in Theorem 6.16(3)

The printed bound v_p(H_(2j)^(beta,2r)) >= -2r is not uniform in j.
At p=7, r=1, j=13 the actual sum contains the odd denominator 49,
and its exact valuation is -4. The prime satisfies p>2k+3 for k=1.
Thus the manuscript's proof-only restriction p>2 sqrt(K) cannot be
dropped from that harmonic estimate. This is a local refutation, not
a disproof of a corrected asymptotic multiplier statement.
-/

namespace ManuscriptChain.Chapter6HarmonicPrimePower

open BetaBeukers

/-- The numerical prime and coefficient-size conditions in 6.16 are satisfied. -/
theorem permitted_prime_and_indices : Nat.Prime 7 ∧ 7 > 2 * 1 + 3 ∧
    1 < 13 ∧ 13 ≤ 14 ∧ 24 < 2 * 13 ∧ 2 * 24 + 1 = 7 ^ 2 := by
  norm_num

/-- Exact rational evaluation of the actual 26-term alternating odd harmonic sum. -/
theorem beta_harmonic_two_twenty_six :
    betaHarmonic 2 26 =
      (8589091807733599182225634358050783803464 : ℚ) /
        9378981288376284666018122686288718555625 := by
  norm_num [betaHarmonic, Finset.sum_range_succ]

/-- After removing its fourth-order 7-pole, both numerator and denominator are units. -/
theorem scaled_harmonic_seven_units :
    ¬ (7 : ℤ) ∣ ((7 : ℚ)^4 * betaHarmonic 2 26).num ∧
    ¬ 7 ∣ ((7 : ℚ)^4 * betaHarmonic 2 26).den := by
  rw [beta_harmonic_two_twenty_six]
  norm_num

/-- The exact valuation is twice as negative as the printed uniform bound. -/
theorem beta_harmonic_prime_square_valuation :
    padicValRat 7 (betaHarmonic 2 26) = -4 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hq : betaHarmonic 2 26 ≠ 0 := by
    rw [beta_harmonic_two_twenty_six]
    norm_num
  have hunit : padicValRat 7 ((7 : ℚ)^4 * betaHarmonic 2 26) = 0 := by
    rw [padicValRat_def,
      padicValInt.eq_zero_of_not_dvd scaled_harmonic_seven_units.1,
      padicValNat.eq_zero_of_not_dvd scaled_harmonic_seven_units.2]
    norm_num
  have hseven : padicValRat 7 (7 : ℚ) = 1 := by
    simpa using (padicValRat.self (p := 7) (by norm_num))
  rw [padicValRat.mul (by norm_num) hq, padicValRat.pow, hseven] at hunit
  omega

/-- The exact harmonic assertion in 6.16(3) fails without a cutoff restriction. -/
theorem printed_uniform_harmonic_bound_false :
    ¬ (-(2 : ℤ) ≤ padicValRat 7 (betaHarmonic 2 (2 * 13))) := by
  rw [show 2 * 13 = 26 by norm_num, beta_harmonic_prime_square_valuation]
  norm_num

end ManuscriptChain.Chapter6HarmonicPrimePower
