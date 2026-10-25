import Zetahyperbolic.Section3.ActualSpectrum

/-!
# Finite reciprocal moments and the sharp root radius

These are the finite-sum inequalities underlying the corrected Corollary 3.6.
Spectral indices retain multiplicity. No distinct-root or distinct-distance
assumption, or all-orders strict Hankel positivity, is used.
-/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.Spectral

variable {n : ℕ}

def evenSpectralMoment (p : SymmetricAffinePencil n) (r : ℕ) : ℝ :=
  ∑ i, |actualEigenvalues p i| ^ (2 * r)

def reciprocalRootMoment (p : SymmetricAffinePencil n) (r : ℕ) : ℝ :=
  ∑ i, (|(p.center - (actualEigenvalues p i)⁻¹) - p.center|⁻¹) ^ (2 * r)

theorem reciprocalRootMoment_eq (p : SymmetricAffinePencil n) (r : ℕ) :
    reciprocalRootMoment p r = evenSpectralMoment p r := by
  have he (i : Fin n) :
      (p.center - (actualEigenvalues p i)⁻¹) - p.center =
        -(actualEigenvalues p i)⁻¹ := by ring
  simp [reciprocalRootMoment, evenSpectralMoment, he, abs_inv]

theorem evenSpectralMoment_bounds (p : SymmetricAffinePencil n)
    (hn : 0 < n) (r : ℕ) :
    actualOperatorNorm p ^ (2*r) ≤ evenSpectralMoment p r ∧
      evenSpectralMoment p r ≤ (n : ℝ) * actualOperatorNorm p ^ (2*r) := by
  constructor
  · obtain ⟨i, hi⟩ := actualOperatorNorm_attained p hn
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin n => |actualEigenvalues p j| ^ (2*r))
      (fun j _ => pow_nonneg (abs_nonneg (actualEigenvalues p j)) (2*r))
      (Finset.mem_univ i)
    rw [hi] at h
    exact h
  · calc
      evenSpectralMoment p r ≤ ∑ _ : Fin n, actualOperatorNorm p ^ (2*r) := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (abs_nonneg _) (actualEigenvalues_abs_le_operatorNorm p i) _
      _ = _ := by simp

theorem evenSpectralMoment_pos (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (hn : 0 < n) (r : ℕ) : 0 < evenSpectralMoment p r :=
  lt_of_lt_of_le (pow_pos (actualOperatorNorm_pos p positive direction_nonzero hn) _)
    (evenSpectralMoment_bounds p hn r).1

/-- The corrected inequalities in a form using only natural powers:
`1 ≤ S_(2r) d_min^(2r) ≤ n`. -/
theorem reciprocalRootMoment_radius_bounds (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (hn : 0 < n) (r : ℕ) :
    1 ≤ reciprocalRootMoment p r * (1 / actualOperatorNorm p) ^ (2*r) ∧
      reciprocalRootMoment p r * (1 / actualOperatorNorm p) ^ (2*r) ≤ (n : ℝ) := by
  rw [reciprocalRootMoment_eq]
  have hn0 := actualOperatorNorm_pos p positive direction_nonzero hn
  have hpow : 0 ≤ (1 / actualOperatorNorm p) ^ (2*r) := by positivity
  have hcancel : actualOperatorNorm p ^ (2*r) *
      (1 / actualOperatorNorm p) ^ (2*r) = 1 := by
    rw [← mul_pow]
    simp [ne_of_gt hn0]
  obtain ⟨hl, hu⟩ := evenSpectralMoment_bounds p hn r
  constructor
  · simpa only [hcancel] using mul_le_mul_of_nonneg_right hl hpow
  · simpa only [mul_assoc, hcancel, mul_one] using mul_le_mul_of_nonneg_right hu hpow

theorem normalized_inverse_power_bounds {S d : ℝ} {n m : ℕ}
    (hS : 0 < S) (hd : 0 < d) (hm : 0 < m)
    (hb : 1 ≤ S * d^m ∧ S * d^m ≤ (n : ℝ)) :
    (n : ℝ) ^ (-((m : ℝ)⁻¹)) ≤ S ^ (-((m : ℝ)⁻¹)) / d ∧
      S ^ (-((m : ℝ)⁻¹)) / d ≤ 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have ht : -((m : ℝ)⁻¹) ≤ 0 :=
    neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg m))
  have he : (S * d^m) ^ (-((m : ℝ)⁻¹)) = S ^ (-((m : ℝ)⁻¹)) / d := by
    rw [Real.mul_rpow hS.le (pow_nonneg hd.le _),
      ← Real.rpow_natCast_mul hd.le, mul_neg, mul_inv_cancel₀ hm0, Real.rpow_neg_one]
    rfl
  constructor
  · rw [← he]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hb.2 ht
  · have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hb.1 ht
    simpa only [he, Real.one_rpow] using h

/-- Corrected Corollary 3.6: the finite-moment estimate approaches the sharp
radius from below, with the factor `n^(-1/(2r))` as a lower bound. -/
theorem reciprocalRootMoment_approximation_bounds (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (direction_nonzero : p.direction.det ≠ 0)
    (hn : 0 < n) (r : ℕ) (hr : 0 < r) :
    (n : ℝ) ^ (-((2*r : ℕ) : ℝ)⁻¹) ≤
        reciprocalRootMoment p r ^ (-((2*r : ℕ) : ℝ)⁻¹) /
          (1 / actualOperatorNorm p) ∧
      reciprocalRootMoment p r ^ (-((2*r : ℕ) : ℝ)⁻¹) /
          (1 / actualOperatorNorm p) ≤ 1 := by
  apply normalized_inverse_power_bounds
  · rw [reciprocalRootMoment_eq]
    exact evenSpectralMoment_pos p positive direction_nonzero hn r
  · exact one_div_pos.mpr (actualOperatorNorm_pos p positive direction_nonzero hn)
  · omega
  · exact reciprocalRootMoment_radius_bounds p positive direction_nonzero hn r

end ManuscriptChain.Spectral

namespace ManuscriptChain

/-- Actual admissible Hankel roots satisfy the corrected finite moment bounds. -/
theorem ACTUAL_RECIPROCAL_MOMENT_BOUNDS (p : Real.Parameters) (hp : Real.Admissible p)
    (r : ℕ) :
    let q := Real.manuscriptPencil p
    1 ≤ Spectral.reciprocalRootMoment q r *
        (1 / Spectral.actualOperatorNorm q) ^ (2*r) ∧
      Spectral.reciprocalRootMoment q r *
        (1 / Spectral.actualOperatorNorm q) ^ (2*r) ≤ (p.h : ℝ) :=
  Spectral.reciprocalRootMoment_radius_bounds (Real.manuscriptPencil p) (GRAM_POSITIVE p hp)
    (General.derivative_nonsingular p) (Nat.sub_pos_of_lt hp.N_lt_K) r

end ManuscriptChain
