import Zetahyperbolic.Section3.MomentGrowth
import Mathlib.Analysis.PSeries

/-!
# Divergence of the concrete Stieltjes Carleman series

The factorial estimate implies a uniform linear bound on the `2r`-th roots
of the moments. The reciprocal roots therefore dominate a positive multiple
of the harmonic series. This verifies the actual Carleman condition; the
separate measure-uniqueness theorem is not assumed or asserted here.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ManuscriptChain.ConcreteMoment

/-- An elementary factorial-to-root bound, deliberately with loose constants. -/
theorem factorial_majorant_le_power {C : ℝ} (hC : 0 ≤ C) (A r : ℕ) (hr : 1 ≤ r) :
    C * (Nat.factorial (2 * r + A) : ℝ) ≤
      (((C + 1) * ((A : ℝ) + 2) ^ (A + 2) * (2 : ℝ) ^ A) * r) ^ (2 * r) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hAR : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hb : (1 : ℝ) ≤ (A : ℝ) + 2 := by
    linarith
  have hbase : ((2 * r + A : ℕ) : ℝ) ≤ ((A : ℝ) + 2) * r := by
    push_cast
    nlinarith [mul_nonneg hAR (sub_nonneg.mpr hrR)]
  have hfact : (Nat.factorial (2 * r + A) : ℝ) ≤
      (((2 * r + A : ℕ) : ℝ)) ^ (2 * r + A) := by
    exact_mod_cast Nat.factorial_le_pow (2 * r + A)
  have hpower := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2 * r + A : ℕ) : ℝ))
    hbase (2 * r + A)
  have hc : C ≤ (C + 1) ^ (2 * r) :=
    (by linarith : C ≤ C + 1).trans (le_self_pow₀ (by linarith) (by omega))
  have hbpow : ((A : ℝ) + 2) ^ (2 * r + A) ≤
      ((A : ℝ) + 2) ^ ((A + 2) * (2 * r)) := by
    apply pow_le_pow_right₀ hb
    have hAr : A ≤ A * r := by simpa using Nat.mul_le_mul_left A hr
    nlinarith [Nat.zero_le (A * r)]
  have hrpow : (r : ℝ) ^ A ≤ (2 : ℝ) ^ (A * (2 * r)) := by
    calc
      _ ≤ ((2 : ℝ) ^ r) ^ A := by
        apply pow_le_pow_left₀ (by positivity)
        have hnat : r ≤ 2 ^ r := (Nat.lt_two_pow_self).le
        exact_mod_cast hnat
      _ = (2 : ℝ) ^ (r * A) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
        simpa only [Nat.mul_comm r A] using
          Nat.mul_le_mul_left A (show r ≤ 2 * r by omega))
  calc
    _ ≤ C * (((A : ℝ) + 2) * r) ^ (2 * r + A) :=
      mul_le_mul_of_nonneg_left (hfact.trans hpower) hC
    _ = (C * ((A : ℝ) + 2) ^ (2 * r + A) * (r : ℝ) ^ A) *
        (r : ℝ) ^ (2 * r) := by
      rw [mul_pow, pow_add, pow_add]
      ring
    _ ≤ ((C + 1) ^ (2 * r) * ((A : ℝ) + 2) ^ ((A + 2) * (2 * r)) *
        (2 : ℝ) ^ (A * (2 * r))) * (r : ℝ) ^ (2 * r) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul _ hrpow (by positivity) (by positivity)
      exact mul_le_mul hc hbpow (by positivity) (by positivity)
    _ = _ := by simp only [mul_pow, pow_mul]

def carlemanOffset (p : Real.Parameters) : ℕ :=
  2 * p.k + 2 * (numeratorPolynomial p).natDegree + 1

def carlemanConstant (p : Real.Parameters) : ℝ :=
  (momentGrowthConstant p + 1) * ((carlemanOffset p : ℝ) + 2) ^ (carlemanOffset p + 2) *
    (2 : ℝ) ^ carlemanOffset p

theorem carlemanConstant_pos (p : Real.Parameters) : 0 < carlemanConstant p := by
  have hC := momentGrowthConstant_pos p
  unfold carlemanConstant
  positivity

theorem moment_le_carleman_power (p : Real.Parameters) (r : ℕ) (hr : 1 ≤ r) :
    (∫ t, t ^ r ∂momentMeasure p) ≤ (carlemanConstant p * r) ^ (2 * r) := by
  have h := moment_le_factorial p r
  have hindex : 2 * p.k + 2 * (r + (numeratorPolynomial p).natDegree) + 1 =
      2 * r + carlemanOffset p := by simp only [carlemanOffset]; omega
  rw [hindex] at h
  exact h.trans (factorial_majorant_le_power (momentGrowthConstant_pos p).le
    (carlemanOffset p) r hr)

def carlemanTerm (p : Real.Parameters) (r : ℕ) : ℝ :=
  (∫ t, t ^ r ∂momentMeasure p) ^ (-(((2 * r : ℕ) : ℝ))⁻¹)

theorem carlemanTerm_lower_bound (p : Real.Parameters) (r : ℕ) (hr : 1 ≤ r) :
    1 / (carlemanConstant p * r) ≤ carlemanTerm p r := by
  have hB := carlemanConstant_pos p
  have hpos : 0 < ∫ t : ℝ, t ^ r ∂momentMeasure p := by
    simpa [Matrix.det_fin_one] using solid_moment_det_pos p r 0 1
  have hbound := moment_le_carleman_power p r hr
  have h := _root_.Real.rpow_le_rpow_of_nonpos hpos hbound
    (by exact neg_nonpos.mpr (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ ((2 * r : ℕ) : ℝ))) :
      -(((2 * r : ℕ) : ℝ))⁻¹ ≤ 0)
  rw [_root_.Real.rpow_neg (by positivity),
    _root_.Real.pow_rpow_inv_natCast (by
      have hb := carlemanConstant_pos p
      positivity) (by omega)] at h
  simpa only [one_div, carlemanTerm] using h

/-- The exact concrete moments satisfy the Stieltjes Carleman divergence
condition, with the index started at one. -/
theorem carlemanSeries_not_summable (p : Real.Parameters) :
    ¬ Summable (fun n : ℕ => carlemanTerm p (n + 1)) := by
  intro hs
  have hsmall : Summable (fun n : ℕ => 1 / (carlemanConstant p * (n + 1))) := by
    apply Summable.of_nonneg_of_le (fun n => by
      have hb := carlemanConstant_pos p
      positivity) _ hs
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using carlemanTerm_lower_bound p (n + 1) (by omega)
  have heq : (fun n : ℕ => 1 / (carlemanConstant p * (n + 1))) =
      (fun n : ℕ => (carlemanConstant p)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ))) := by
    funext n
    simp [one_div, mul_inv_rev, mul_comm]
  rw [heq] at hsmall
  have hsum := (summable_mul_left_iff (inv_ne_zero (carlemanConstant_pos p).ne')).1 hsmall
  exact _root_.Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 hsum)

end ManuscriptChain.ConcreteMoment

