import Zetahyperbolic.Section5.BetaBeukersMoments
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Corrected all-order odd-harmonic valuation bound

The number of allowed prime powers depends on the actual largest odd
denominator. The cutoff 2M <= p^(a+1) bounds every denominator valuation by a.
For the sum H_(2j) used in 6.16, the printed -s bound is valid when 4j <= p^2.
This includes arbitrary weights and proves the bound from the literal finite
alternating harmonic sum, without a valuation premise on that sum.
-/

namespace ManuscriptChain.Chapter6HarmonicCutoff

open BetaBeukers

private theorem finite_sum_lower (p : ℕ) [Fact p.Prime]
    (c : ℤ) (hc : c ≤ 0) (F : ℕ → ℚ) :
    ∀ n : ℕ, (∀ i : ℕ, i < n → c ≤ padicValRat p (F i)) →
      c ≤ padicValRat p (∑ i ∈ Finset.range n, F i) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using hc
  | succ n ih =>
      intro hF
      rw [Finset.sum_range_succ]
      by_cases hz : (∑ i ∈ Finset.range n, F i) + F n = 0
      · rw [hz, padicValRat.zero]
        exact hc
      · exact (le_min (ih (fun i hi => hF i (by omega)))
          (hF n (by omega))).trans (padicValRat.min_le_padicValRat_add hz)

/-- Correct prime-power bound for the actual alternating odd harmonic sum. -/
theorem beta_harmonic_valuation_lower (p s M a : ℕ) [Fact p.Prime]
    (hM : 2 * M ≤ p ^ (a + 1)) :
    -(s : ℤ) * (a : ℤ) ≤ padicValRat p (betaHarmonic s M) := by
  unfold betaHarmonic
  apply finite_sum_lower p (-(s : ℤ) * (a : ℤ))
    (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg s)) (Nat.cast_nonneg a))
  intro i hi
  have hden : 0 < 2 * i + 1 := by omega
  have hpower : 2 * i + 1 < p ^ (a + 1) := by omega
  have hlog := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hden) hpower
  have hval := padicValNat_le_nat_log (p := p) (2 * i + 1)
  have hbound : padicValNat p (2 * i + 1) ≤ a := by omega
  have hsign : (-1 : ℚ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdenQ : (((2 * i + 1 : ℕ) : ℚ) ^ s) ≠ 0 := by positivity
  rw [padicValRat.div hsign hdenQ]
  simp only [padicValRat.pow, padicValRat.neg, padicValRat.one,
    mul_zero, padicValRat.of_nat, zero_sub]
  have hboundZ : (padicValNat p (2 * i + 1) : ℤ) ≤ (a : ℤ) := by
    exact_mod_cast hbound
  have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg s
  nlinarith

/-- The intended bound in 6.16, with an explicit sufficient prime-size cutoff. -/
theorem beta_even_index_bound_before_prime_square (p s j : ℕ) [Fact p.Prime]
    (hj : 4 * j ≤ p ^ 2) :
    -(s : ℤ) ≤ padicValRat p (betaHarmonic s (2 * j)) := by
  simpa using beta_harmonic_valuation_lower p s (2 * j) 1 (by
    change 2 * (2 * j) ≤ p ^ 2
    omega)

/-- The zero-pole window uses the actual odd denominator cutoff. -/
theorem beta_harmonic_integral_before_prime (p s M : ℕ) [Fact p.Prime]
    (hM : 2 * M ≤ p) : 0 ≤ padicValRat p (betaHarmonic s M) := by
  simpa using beta_harmonic_valuation_lower p s M 0 (by simpa using hM)

end ManuscriptChain.Chapter6HarmonicCutoff
