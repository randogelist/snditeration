import Zetahyperbolic.Section3.ActualSpectrum

/-!
# Finite roots and sharp radius when principal slopes may be singular

Zero eigenvalues contribute constant factors. Every nonzero eigenvalue gives a
finite root, and a positive operator norm gives an attained sharp root radius.
-/
noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace ManuscriptChain.Spectral
variable {n : ℕ}

/-- Actual spectral root description without an invertibility premise on the slope. -/
theorem actual_complex_root_iff_allow_singular (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 ↔
      ∃ i, actualEigenvalues p i ≠ 0 ∧
        z = ((p.center - (actualEigenvalues p i)⁻¹ : ℝ) : ℂ) := by
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      (p.base.det : ℂ) * ∏ i, (1 + (z - (p.center : ℂ)) * (actualEigenvalues p i : ℂ)) := by
    rw [detPolynomial_actual_factorization p positive]
    simp [spectralFactor, Polynomial.eval₂_finsetProd]
  rw [heval]
  have hd : (p.base.det : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive.det_pos)
  constructor
  · intro hz
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hd)
    have hb : actualEigenvalues p i ≠ 0 := by
      intro hzero
      simp [hzero] at hi
    refine ⟨i, hb, ?_⟩
    have he := (linear_factor_eq_zero_iff (p.center : ℂ) (actualEigenvalues p i : ℂ) z
      (Complex.ofReal_ne_zero.mpr hb)).mp hi
    simpa only [Complex.ofReal_sub, Complex.ofReal_inv] using he
  · rintro ⟨i, hb, rfl⟩
    apply mul_eq_zero.mpr
    right
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply (linear_factor_eq_zero_iff (p.center : ℂ) (actualEigenvalues p i : ℂ) _
      (Complex.ofReal_ne_zero.mpr hb)).mpr
    simp

theorem spectral_root_distance (c b : ℝ) :
    ‖((c - b⁻¹ : ℝ) : ℂ) - (c : ℂ)‖ = 1 / |b| := by
  have h : |c - b⁻¹ - c| = 1 / |b| := by
    rw [show c - b⁻¹ - c = -b⁻¹ by ring, abs_neg, abs_inv, one_div]
  simpa [← Complex.ofReal_sub] using h

/-- Every finite root obeys the operator radius bound, even for singular directions. -/
theorem actual_root_distance_allow_singular (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    1 / actualOperatorNorm p ≤ ‖z - (p.center : ℂ)‖ := by
  obtain ⟨i, hi, rfl⟩ := (actual_complex_root_iff_allow_singular p positive z).mp hz
  have habs : 0 < |actualEigenvalues p i| := abs_pos.mpr hi
  rw [spectral_root_distance]
  exact one_div_le_one_div_of_le habs (actualEigenvalues_abs_le_operatorNorm p i)

/-- A nonconstant positive-base pencil has the same sharp operator-norm radius,
regardless of how many zero slopes its principal restriction contains. -/
theorem actual_sharp_radius_allow_singular (p : SymmetricAffinePencil n)
    (positive : p.base.PosDef) (hn : 0 < n) (hpos : 0 < actualOperatorNorm p) :
    (∀ z : ℂ, ‖z - (p.center : ℂ)‖ < 1 / actualOperatorNorm p →
      Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial ≠ 0) ∧
    (∃ z : ℂ, Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0 ∧
      ‖z - (p.center : ℂ)‖ = 1 / actualOperatorNorm p) := by
  constructor
  · intro z hz hr
    exact (not_lt_of_ge (actual_root_distance_allow_singular p positive z hr)) hz
  · obtain ⟨i, hi⟩ := actualOperatorNorm_attained p hn
    have hbi : actualEigenvalues p i ≠ 0 := by
      have : 0 < |actualEigenvalues p i| := by rwa [hi]
      exact abs_pos.mp this
    refine ⟨((p.center - (actualEigenvalues p i)⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · exact (actual_complex_root_iff_allow_singular p positive _).mpr ⟨i, hbi, rfl⟩
    · rw [spectral_root_distance, hi]

end ManuscriptChain.Spectral
