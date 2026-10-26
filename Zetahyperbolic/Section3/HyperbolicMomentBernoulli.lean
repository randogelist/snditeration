import Zetahyperbolic.Section3.HyperbolicMomentExp

/-!
Polynomial moments of the hyperbolic density, part II.

Proves the *actual manuscript monomial formula* (2.2) at ζ(2e+2)
via the classical even-zeta Bernoulli identity. The pole moment
formula remains separate.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem monomial_density_eq_tsum (k e : ℕ) (y : ℝ) :
    y ^ (2 * e) * density k y =
      (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        ∑' n, momentTerm k e n y := by
  unfold density
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold exponentialTerm momentTerm
  have he : 2 * k + 2 * e + 1 = 2 * e + (2 * k + 1) := by omega
  rw [he, pow_add]
  have hx : -(2 * Real.pi * y) * ((n + 1 : ℕ) : ℝ) =
      -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y) := by ring
  rw [hx]
  ring

theorem integrableOn_monomial_density (k e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * density k y) (Ioi 0) := by
  simp_rw [monomial_density_eq_tsum]
  exact (integrableOn_tsum_momentTerm k e).const_mul _

theorem integral_monomial_density (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density k y) =
      (2 * (Nat.factorial (2 * k + 2 * e + 1) : ℝ) /
        ((Nat.factorial (2 * k) : ℝ) * (2 * Real.pi) ^ (2 * e + 2))) *
          Real.zeta (2 * e + 2) := by
  simp_rw [monomial_density_eq_tsum]
  rw [integral_const_mul, integral_tsum_momentTerm]
  unfold momentCoefficient
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  rw [show 2 * k + 2 * e + 2 = 2 * k + (2 * e + 2) by omega, pow_add]
  field_simp

theorem zeta_even_bernoulli (e : ℕ) :
    Real.zeta (2 * e + 2) =
      (-1 : ℝ) ^ e * (2 * Real.pi) ^ (2 * e + 2) *
        (bernoulli (2 * e + 2) : ℝ) /
          (2 * (Nat.factorial (2 * e + 2) : ℝ)) := by
  have hs := hasSum_zeta_nat (k := e + 1) (by omega)
  have hz : Real.zeta (2 * e + 2) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * (e + 1)) := by
    rw [hs.summable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, show 2 * (e + 1) ≠ 0 by omega, ne_eq, not_false_eq_true,
      zero_pow, div_zero, zero_add]
    congr 1
  rw [hz, hs.tsum_eq]
  have h1 : 2 * (e + 1) = 2 * e + 2 := by omega
  have h2 : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
  rw [h2, h1, show e + 1 + 1 = e + 2 by omega,
    pow_add (-1 : ℝ), pow_succ (2 : ℝ) (2 * e), mul_pow]
  norm_num
  rw [show 2 * e + 2 = (2 * e + 1) + 1 by omega, pow_succ, pow_succ]
  ring

theorem integral_monomial_density_eq_monomialMoment (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density k y) =
      (Real.monomialMoment k e : ℝ) := by
  rw [integral_monomial_density, zeta_even_bernoulli]
  unfold Real.monomialMoment
  push_cast
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  have hg : (Nat.factorial (2 * e + 2) : ℝ) ≠ 0 := by positivity
  rw [show 2 * e + 2 * k + 1 = 2 * k + 2 * e + 1 by omega]
  field_simp

end ManuscriptChain.Hyperbolic
