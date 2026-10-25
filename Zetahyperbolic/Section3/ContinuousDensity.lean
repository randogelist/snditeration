import Zetahyperbolic.Section3.HyperbolicMomentBernoulli

/-!
The corrected real-weight density of Proposition 3.2. The printed prefactor
is too large by π/2. This module constructs the real-parameter density and
proves its positivity, integrability and exact moments, without an analytic
integrability premise.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.ContinuousWeight

def exponentialTerm (s : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (s - 1) *
    Real.exp (-(2 * Real.pi * y) * ((n + 1 : ℕ) : ℝ))

def prefactor (s : ℝ) : ℝ := 2 * (2 * Real.pi) ^ (s - 1) / Real.Gamma s

def density (s y : ℝ) : ℝ := prefactor s * y ^ s * ∑' n, exponentialTerm s n y

theorem summable_exponentialTerm (s : ℝ) {y : ℝ} (hy : 0 < y) :
    Summable (fun n => exponentialTerm s n y) := by
  obtain ⟨d, hd⟩ := exists_nat_ge (s - 1)
  have hsum := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul d
      (show 0 < 2 * Real.pi * y by positivity))
  apply Summable.of_nonneg_of_le (fun n => by unfold exponentialTerm; positivity) _ hsum
  intro n
  unfold exponentialTerm
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hd

theorem exponentialTerm_pos (s : ℝ) (n : ℕ) (y : ℝ) :
    0 < exponentialTerm s n y := by unfold exponentialTerm; positivity

theorem prefactor_pos {s : ℝ} (hs : 0 < s) : 0 < prefactor s := by
  unfold prefactor
  exact div_pos (by positivity) (Real.Gamma_pos_of_pos hs)

theorem density_pos {s y : ℝ} (hs : 0 < s) (hy : 0 < y) : 0 < density s y := by
  exact mul_pos (mul_pos (prefactor_pos hs) (Real.rpow_pos_of_pos hy _))
    ((summable_exponentialTerm s hy).tsum_pos
      (fun n => (exponentialTerm_pos s n y).le) 0 (exponentialTerm_pos s 0 y))

theorem measurable_density (s : ℝ) : Measurable (density s) := by
  unfold density exponentialTerm
  exact (measurable_const.mul (measurable_id.pow measurable_const)).mul
    (Measurable.tsum (fun n => by fun_prop))

theorem prefactor_odd (k : ℕ) :
    prefactor (2 * (k : ℝ) + 1) =
      2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) := by
  unfold prefactor
  rw [show 2 * (k : ℝ) + 1 = ((2 * k : ℕ) : ℝ) + 1 by push_cast; rfl,
    Real.Gamma_nat_eq_factorial]
  rw [add_sub_cancel_right, Real.rpow_natCast]

theorem density_odd (k : ℕ) (y : ℝ) :
    density (2 * (k : ℝ) + 1) y = Hyperbolic.density k y := by
  unfold density Hyperbolic.density
  rw [prefactor_odd]
  have he : 2 * (k : ℝ) + 1 = ((2 * k + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast]
  congr 2
  funext n
  unfold exponentialTerm Hyperbolic.exponentialTerm
  rw [show ((2 * k + 1 : ℕ) : ℝ) - 1 = ((2 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

def momentTerm (s : ℝ) (e n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (s - 1) *
    (y ^ (s + 2 * e) * Real.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y)))

def momentCoefficient (s : ℝ) (e : ℕ) : ℝ :=
  Real.Gamma (s + 2 * e + 1) / (2 * Real.pi) ^ (s + 2 * e + 1)

theorem integral_rpow_exp {d a : ℝ} (hd : -1 < d) (ha : 0 < a) :
    (∫ y : ℝ in Ioi 0, y ^ d * Real.exp (-(a * y))) =
      Real.Gamma (d + 1) / a ^ (d + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := d + 1) (r := a) (by linarith) ha
  rw [one_div, Real.inv_rpow ha.le] at h
  simpa [div_eq_mul_inv, mul_comm] using h

theorem momentTerm_integrable {s : ℝ} (hs : 0 < s) (e n : ℕ) :
    IntegrableOn (momentTerm s e n) (Ioi 0) := by
  unfold momentTerm
  apply Integrable.const_mul
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_exp (by linarith [Nat.cast_nonneg (α := ℝ) e]) (by positivity)]
  exact ne_of_gt (div_pos (Real.Gamma_pos_of_pos (by positivity)) (by positivity))

theorem integral_momentTerm {s : ℝ} (hs : 0 < s) (e n : ℕ) :
    (∫ y : ℝ in Ioi 0, momentTerm s e n y) =
      momentCoefficient s e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
  unfold momentTerm momentCoefficient
  rw [integral_const_mul, integral_rpow_exp (by linarith [Nat.cast_nonneg (α := ℝ) e]) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have he : s + 2 * (e : ℝ) + 1 = (s - 1) + ((2 * e + 2 : ℕ) : ℝ) := by
    push_cast; ring
  rw [he, Real.rpow_add hn, Real.rpow_natCast]
  field_simp

theorem summable_integral_norm {s : ℝ} (hs : 0 < s) (e : ℕ) :
    Summable (fun n => ∫ y : ℝ in Ioi 0, ‖momentTerm s e n y‖) := by
  have h (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖momentTerm s e n y‖) =
      momentCoefficient s e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
    rw [← integral_momentTerm hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (mul_nonneg (Real.rpow_nonneg hy.le _) (Real.exp_pos _).le))
  simp_rw [h]
  exact (Real.zeta_series_summable (s := 2 * e + 2) (by omega)).mul_left _

theorem integral_tsum_momentTerm {s : ℝ} (hs : 0 < s) (e : ℕ) :
    (∫ y : ℝ in Ioi 0, ∑' n, momentTerm s e n y) =
      momentCoefficient s e * Real.zeta (2 * e + 2) := by
  rw [← integral_tsum_of_summable_integral_norm (momentTerm_integrable hs e)
    (summable_integral_norm hs e)]
  simp_rw [integral_momentTerm hs]
  rw [tsum_mul_left]
  rfl

theorem monomial_density_eq_tsum (s : ℝ) (e : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ (2 * e) * density s y = prefactor s * ∑' n, momentTerm s e n y := by
  unfold density
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold exponentialTerm momentTerm
  rw [Real.rpow_add hy, show (2 : ℝ) * e = ((2 * e : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast]
  rw [show -(2 * Real.pi * y) * ((n + 1 : ℕ) : ℝ) =
    -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y) by ring]
  ring

theorem integrableOn_monomial_density {s : ℝ} (hs : 0 < s) (e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * density s y) (Ioi 0) := by
  have hi : IntegrableOn (fun y : ℝ => ∑' n, momentTerm s e n y) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_tsum_momentTerm hs]
    exact ne_of_gt (mul_pos (by unfold momentCoefficient; positivity)
      (Real.zeta_pos (by omega)))
  apply (hi.const_mul (prefactor s)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (monomial_density_eq_tsum s e hy).symm

theorem integral_monomial_density {s : ℝ} (hs : 0 < s) (e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density s y) =
      prefactor s * momentCoefficient s e * Real.zeta (2 * e + 2) := by
  calc
    _ = ∫ y : ℝ in Ioi 0, prefactor s * ∑' n, momentTerm s e n y :=
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => monomial_density_eq_tsum s e hy)
    _ = _ := by rw [integral_const_mul, integral_tsum_momentTerm hs, mul_assoc]

end ManuscriptChain.ContinuousWeight
