import Zetahyperbolic.Section2.TauGenerators

/-!
# The polynomial finite-difference identity for τ

The Bernoulli convolution has one exceptional index, B₁. That exception
makes τ(p(X+1)-p(X)) exactly the coefficient of X^(2k) in p.
This supplies the polynomial contribution to Lemma 2.3(2).
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Tau

lemma tauPolynomial_shifted_power_sub (k d : ℕ) (hk : 1 ≤ k) :
    tauPolynomial k ((X+1 : ℚ[X])^d) - tauPolynomial k (X^d) =
      if d = 2*k then 1 else 0 := by
  rw [add_comm (X : ℚ[X]), tauPolynomial_one_add_X_pow, tauPolynomial_X_pow]
  by_cases hd : 2*k-1 ≤ d
  · rw [tauMonomial_binomial_convolution k d hk hd,
      tauMonomial_eq_choose k d hk, if_pos hd]
    by_cases he : d = 2*k
    · subst d
      have hn : 2*k-(2*k-1) = 1 := by omega
      have hc : Nat.choose (2*k) (2*k-1) = 2*k := by
        rw [← Nat.choose_symm (show 2*k-1 ≤ 2*k by omega), hn]
        simp
      have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      norm_num [hn, hc, bernoulli_one, bernoulli'_one, hkQ]
    · have hn : d-(2*k-1) ≠ 1 := by omega
      rw [if_neg he, ← bernoulli_eq_bernoulli'_of_ne_one hn]
      ring
  · have hzero : ∀ i ∈ Finset.range (d+1), tauMonomial k i = 0 := by
      intro i hi
      have hi' : i < d+1 := Finset.mem_range.mp hi
      have hcut : ¬ 2*k-1 ≤ i := by omega
      simp [tauMonomial, hcut]
    have hsum : (∑ i ∈ Finset.range (d+1), (Nat.choose d i : ℚ) * tauMonomial k i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i hi, mul_zero]
    rw [hsum]
    have he : d ≠ 2*k := by omega
    simp [tauMonomial, hd, he]

/-- The polynomial part of Lemma 2.3's finite-difference identity, on every
actual polynomial rather than only individual monomials. -/
theorem tauPolynomial_difference (k : ℕ) (hk : 1 ≤ k) (p : ℚ[X]) :
    tauPolynomial k (p.comp (X+1) - p) = p.coeff (2*k) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, add_sub_add_comm, map_add, hp, hq, Polynomial.coeff_add]
  | monomial d a =>
    have heq : (monomial d a).comp (X+1) - monomial d a =
        a • ((X+1 : ℚ[X])^d - X^d) := by
      rw [Polynomial.monomial_comp, Polynomial.smul_eq_C_mul,
        ← Polynomial.C_mul_X_pow_eq_monomial]
      ring
    rw [heq, map_smul, map_sub, tauPolynomial_shifted_power_sub k d hk]
    by_cases he : d = 2*k
    · simp [he]
    · simp [Polynomial.coeff_monomial, he]

end ManuscriptChain.Tau
