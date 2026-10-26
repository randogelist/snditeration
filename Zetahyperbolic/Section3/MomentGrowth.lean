import Zetahyperbolic.Section3.ShiftedMomentPositivity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Explicit factorial bounds for the concrete moments

The tail denominator is at least one. Expanding the remaining polynomial and
using the exact hyperbolic moments gives a uniform factorial majorant. The
constants are explicit functions of the actual numerator coefficients; no
moment-growth hypothesis is supplied by the caller.

This establishes a growth estimate used in a Carleman argument. Stieltjes
determinacy itself is not claimed here.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace ManuscriptChain.Hyperbolic

theorem zeta_even_le_zeta_two (e : ℕ) : Real.zeta (2 * e + 2) ≤ Real.zeta 2 := by
  apply Summable.tsum_le_tsum _ (Real.zeta_series_summable (by omega))
    (Real.zeta_series_summable (by omega))
  intro n
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀
  · exact_mod_cast (show 1 ≤ n + 1 by omega)
  · omega

theorem integral_monomial_density_le_factorial (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density k y) ≤
      2 * Real.zeta 2 * (Nat.factorial (2 * k + 2 * e + 1) : ℝ) := by
  rw [integral_monomial_density]
  have hf : (1 : ℝ) ≤ Nat.factorial (2 * k) := by
    exact_mod_cast (show 1 ≤ Nat.factorial (2 * k) from Nat.factorial_pos (2 * k))
  have hp : (1 : ℝ) ≤ (2 * _root_.Real.pi) ^ (2 * e + 2) := by
    apply one_le_pow₀
    linarith [_root_.Real.pi_gt_three]
  have hd : (1 : ℝ) ≤ (Nat.factorial (2 * k) : ℝ) *
      (2 * _root_.Real.pi) ^ (2 * e + 2) := one_le_mul_of_one_le_of_one_le hf hp
  have hb := div_le_self (show (0 : ℝ) ≤
    2 * (Nat.factorial (2 * k + 2 * e + 1) : ℝ) by positivity) hd
  have hz := zeta_even_le_zeta_two e
  calc
    _ ≤ (2 * (Nat.factorial (2 * k + 2 * e + 1) : ℝ)) *
        Real.zeta (2 * e + 2) :=
      mul_le_mul_of_nonneg_right hb (Real.zeta_pos (by omega)).le
    _ ≤ (2 * (Nat.factorial (2 * k + 2 * e + 1) : ℝ)) * Real.zeta 2 :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring

theorem integral_real_polynomial_density (k : ℕ) (q : ℝ[X]) :
    (∫ y : ℝ in Ioi 0, q.eval (y ^ 2) * density k y) =
      ∑ e ∈ q.support, q.coeff e *
        (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density k y) := by
  have hfun : (fun y : ℝ => q.eval (y ^ 2) * density k y) =
      fun y => ∑ e ∈ q.support, q.coeff e * (y ^ (2 * e) * density k y) := by
    funext y
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [← pow_mul]
    ring
  rw [hfun, integral_finsetSum _ (fun e _ =>
    (integrableOn_monomial_density k e).const_mul (q.coeff e))]
  simp_rw [integral_const_mul]

end ManuscriptChain.Hyperbolic

namespace ManuscriptChain.ConcreteMoment

def numeratorPolynomial (p : Real.Parameters) : ℝ[X] :=
  Real.realPolynomial (Real.D p.N ^ (2 * p.m - 1))

def momentGrowthConstant (p : Real.Parameters) : ℝ :=
  2 * Real.zeta 2 * ∑ e ∈ (numeratorPolynomial p).support,
    |(numeratorPolynomial p).coeff e|

theorem moment_le_numerator_integral (p : Real.Parameters) (r : ℕ) :
    (∫ t, t ^ r ∂momentMeasure p) ≤
      ∫ y : ℝ in Ioi 0,
        ((numeratorPolynomial p) * X ^ r).eval (y ^ 2) * Hyperbolic.density p.k y := by
  rw [integral_momentMeasure]
  apply integral_mono_ae (integrableOn_weightedDensity_moment p r)
    (integrableOn_polynomial_density p.k _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hN : 0 ≤ Real.evalQ (Real.D p.N ^ (2 * p.m - 1)) (y ^ 2) := by
    have h := (evalQ_D_pos p.N (sq_pos_of_pos hy)).le
    simpa [Real.evalQ, Real.realPolynomial] using pow_nonneg h (2 * p.m - 1)
  have hratio := div_le_self hN (evalQ_tailD_ge_one p (sq_nonneg y))
  have hmul := mul_le_mul_of_nonneg_right hratio (Hyperbolic.density_pos p.k hy).le
  have htotal := mul_le_mul_of_nonneg_left hmul (pow_nonneg hy.le (2 * r))
  simpa [weightedDensity, numeratorPolynomial, Real.evalQ, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul, mul_assoc, mul_left_comm, mul_comm]
    using htotal

theorem integral_numerator_moment (p : Real.Parameters) (r : ℕ) :
    (∫ y : ℝ in Ioi 0,
      ((numeratorPolynomial p) * X ^ r).eval (y ^ 2) * Hyperbolic.density p.k y) =
      ∑ e ∈ (numeratorPolynomial p).support, (numeratorPolynomial p).coeff e *
        (∫ y : ℝ in Ioi 0, y ^ (2 * (r + e)) * Hyperbolic.density p.k y) := by
  have hfun : (fun y : ℝ =>
      ((numeratorPolynomial p) * X ^ r).eval (y ^ 2) * Hyperbolic.density p.k y) =
      fun y => ∑ e ∈ (numeratorPolynomial p).support,
        (numeratorPolynomial p).coeff e * (y ^ (2 * (r + e)) * Hyperbolic.density p.k y) := by
    funext y
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_eq_sum]
    simp only [Polynomial.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [Nat.mul_add, pow_add, pow_mul, pow_mul]
    ring
  rw [hfun, integral_finsetSum _ (fun e _ =>
    (Hyperbolic.integrableOn_monomial_density p.k (r + e)).const_mul _)]
  simp_rw [integral_const_mul]

/-- Explicit factorial growth for every actual moment, with no asymptotic
or comparison assumption. -/
theorem moment_le_factorial (p : Real.Parameters) (r : ℕ) :
    (∫ t, t ^ r ∂momentMeasure p) ≤
      momentGrowthConstant p *
        (Nat.factorial (2 * p.k + 2 * (r + (numeratorPolynomial p).natDegree) + 1) : ℝ) := by
  apply (moment_le_numerator_integral p r).trans
  rw [integral_numerator_moment]
  unfold momentGrowthConstant
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e he
  have hedeg : e ≤ (numeratorPolynomial p).natDegree := Polynomial.le_natDegree_of_mem_supp e he
  have hfact : (Nat.factorial (2 * p.k + 2 * (r + e) + 1) : ℝ) ≤
      (Nat.factorial (2 * p.k + 2 * (r + (numeratorPolynomial p).natDegree) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (show 2 * p.k + 2 * (r + e) + 1 ≤
      2 * p.k + 2 * (r + (numeratorPolynomial p).natDegree) + 1 by omega)
  have hbase := (Hyperbolic.integral_monomial_density_le_factorial p.k (r + e)).trans
    (mul_le_mul_of_nonneg_left hfact (by
      have hz := Real.zeta_pos (s := 2) (by omega)
      positivity : 0 ≤ 2 * Real.zeta 2))
  have hpos : 0 ≤ ∫ y : ℝ in Ioi 0,
      y ^ (2 * (r + e)) * Hyperbolic.density p.k y := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (pow_nonneg hy.le _) (Hyperbolic.density_pos p.k hy).le
  calc
    _ ≤ |(numeratorPolynomial p).coeff e| *
        (∫ y : ℝ in Ioi 0, y ^ (2 * (r + e)) * Hyperbolic.density p.k y) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    _ ≤ |(numeratorPolynomial p).coeff e| *
        (2 * Real.zeta 2 *
          (Nat.factorial (2 * p.k + 2 * (r + (numeratorPolynomial p).natDegree) + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase (abs_nonneg _)
    _ = _ := by ring

theorem momentGrowthConstant_pos (p : Real.Parameters) : 0 < momentGrowthConstant p := by
  have hpos : 0 < ∫ t : ℝ, t ^ 0 ∂momentMeasure p := by
    have h := solid_moment_det_pos p 0 0 1
    erw [Matrix.det_fin_one] at h
    simpa using h
  have hbound := moment_le_factorial p 0
  have hproduct := hpos.trans_le hbound
  exact (mul_pos_iff_of_pos_right (by positivity)).1 hproduct

end ManuscriptChain.ConcreteMoment
