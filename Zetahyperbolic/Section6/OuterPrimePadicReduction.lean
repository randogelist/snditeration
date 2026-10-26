import Zetahyperbolic.Section6.OuterPrimePadicBlock
import Zetahyperbolic.Section6.OuterHarmonicBound

/-! Exact local congruence for the actual scaled weight-seven block.
The norm `<1` means reduction to zero modulo the maximal ideal of Z_p. -/

noncomputable section
open scoped Matrix BigOperators
namespace ManuscriptChain.Beukers

private lemma integral_cast_norm (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : 0 ≤ padicValRat p q) : ‖(q : ℚ_[p])‖ ≤ 1 := by
  by_cases hn : q = 0
  · simp [hn]
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hn]
  exact_mod_cast (zpow_le_one_of_nonpos₀
    (show (1 : ℚ) ≤ p by exact_mod_cast (Fact.out : p.Prime).one_le)
    (neg_nonpos.mpr hq))

private lemma small_power_mul (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≠ 0)
    (a : ℚ_[p]) (ha : ‖a‖ ≤ 1) : ‖(p : ℚ_[p])^n * a‖ < 1 := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ‖(p : ℚ_[p])‖^n * 1 := mul_le_mul_of_nonneg_left ha (by positivity)
    _ < 1 := by
      rw [mul_one]
      exact pow_lt_one₀ (norm_nonneg _) (Padic.norm_p_lt_one (p := p)) hn

def padicLeadingMatrix (p : ℕ) [Fact p.Prime] : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![0, (6 : ℚ_[p])⁻¹; (6 : ℚ_[p])⁻¹, -1]

/-- The actual two-by-two matrix has exactly the printed leading residue.
This proves all four entries simultaneously, at every p-integral p-adic X. -/
theorem padicLocalMatrix_scaled_reduction (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ∀ i j, ‖(p : ℚ_[p])^7 * padicLocalMatrix p r X i j -
      padicLeadingMatrix p i j‖ < 1 := by
  let E (s : ℕ) : ℚ := Real.harmonic s (r+p) - Real.harmonic s r - 1/(p : ℚ)^s
  have hE (s : ℕ) : ‖(E s : ℚ_[p])‖ ≤ 1 :=
    integral_cast_norm p (E s) (harmonic_outer_regular_valuation_nonneg p r s hr)
  have hp : p.Prime := Fact.out
  have hpn : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hsix : (6 : ℚ_[p]) ≠ 0 := by norm_num
  have hnormsix : ‖(6 : ℚ_[p])‖ = 1 := by
    change ‖((6 : ℕ) : ℚ_[p])‖ = 1
    rw [Padic.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega))
  have hlow := padicLocalMatrix_low_norm p r hr X hX
  have hhigherror : ‖(X - (Real.harmonic 7 r : ℚ_[p])) - (E 7 : ℚ_[p])‖ ≤ 1 := by
    simpa only [sub_eq_add_neg] using
      (Padic.nonarchimedean (X - (Real.harmonic 7 r : ℚ_[p])) (-(E 7 : ℚ_[p]))).trans
        (max_le hlow (by simpa only [norm_neg] using hE 7))
  have hdiag : ‖(p : ℚ_[p])^7 * (X - (Real.harmonic 7 (r+p) : ℚ_[p])) + 1‖ < 1 := by
    have he : (p : ℚ_[p])^7 * (X - (Real.harmonic 7 (r+p) : ℚ_[p])) + 1 =
        (p : ℚ_[p])^7 * ((X - (Real.harmonic 7 r : ℚ_[p])) - (E 7 : ℚ_[p])) := by
      dsimp [E]
      push_cast
      field_simp [hpn]
      <;> ring
    rw [he]
    exact small_power_mul p 7 (by norm_num) _ hhigherror
  have hoff : ‖(p : ℚ_[p])^7 * (Real.dualConstant 7 r (r+p) : ℚ_[p]) -
      (6 : ℚ_[p])⁻¹‖ < 1 := by
    have hne : r ≠ r+p := by omega
    have he : (p : ℚ_[p])^7 * (Real.dualConstant 7 r (r+p) : ℚ_[p]) -
        (6 : ℚ_[p])⁻¹ = (p : ℚ_[p])^6 * ((E 6 : ℚ_[p]) / 6) := by
      simp only [Real.dualConstant, if_neg hne]
      norm_num only [Nat.reduceSub, Nat.cast_ofNat]
      dsimp [E]
      push_cast
      field_simp [hpn, hsix]
      <;> ring
    rw [he]
    apply small_power_mul p 6 (by norm_num)
    simpa only [norm_div, hnormsix, div_one] using hE 6
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [padicLocalMatrix, padicLeadingMatrix] using
      small_power_mul p 7 (by norm_num) _ hlow
  · simpa [padicLocalMatrix, padicLeadingMatrix] using hoff
  · simpa [padicLocalMatrix, padicLeadingMatrix] using hoff
  · simpa [padicLocalMatrix, padicLeadingMatrix] using hdiag

end ManuscriptChain.Beukers
