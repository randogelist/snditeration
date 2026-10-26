import Zetahyperbolic.Section6.BetaOddPencil
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! Exact local poles of the printed beta(4) functional. The central odd
denominator has a first-order pole; every later odd denominator before
2p has a fourth-order pole. The residue-polynomial and determinant steps
of Theorem 6.5 are separate from these functional-value estimates. -/

noncomputable section
open scoped BigOperators
namespace ManuscriptChain.BetaOddPoleNorm
open BetaOddPencil

private theorem add_norm_le_one (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (Padic.nonarchimedean a b).trans (max_le ha hb)

private theorem sub_norm_le_one (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  simpa only [sub_eq_add_neg, norm_neg] using
    add_norm_le_one p a (-b) ha (by simpa only [norm_neg] using hb)

private theorem nat_unit_norm (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hnp : n < 2 * p) (hne : n ≠ p) : ‖(n : ℚ_[p])‖ = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  rintro ⟨k, hk⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hklt : k < 2 := by
    apply (Nat.mul_lt_mul_left hp).mp
    rw [← hk]
    exact hnp
  have hk0 : k ≠ 0 := by intro hz; simp [hz] at hk; omega
  have hk1 : k = 1 := by omega
  apply hne
  simpa [hk1] using hk

private theorem sum_norm_le_one (p : ℕ) [Fact p.Prime]
    {ι : Type*} (S : Finset ι) (f : ι → ℚ_[p])
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) : ‖∑ i ∈ S, f i‖ ≤ 1 :=
  norm_sum_le_of_forall_le_of_nonneg (by norm_num) hf

theorem betaHarmonic_below_norm (p N j : ℕ) [Fact p.Prime]
    (hNp : 2 * N + 1 = p) (hj : j ≤ N) :
    ‖(betaHarmonic j : ℚ_[p])‖ ≤ 1 := by
  unfold betaHarmonic
  push_cast
  apply sum_norm_le_one p
  intro n hn
  have hn' := Finset.mem_range.mp hn
  have hunit := nat_unit_norm p (2 * n + 1) (by omega) (by omega) (by omega)
  have hunit' : ‖(2 * (n : ℚ_[p]) + 1)‖ = 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hunit
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, hunit', div_one, le_refl]

/-- Removing the unique odd denominator p leaves an integral remainder. -/
theorem betaHarmonic_regular_norm (p N j : ℕ) [Fact p.Prime]
    (hNp : 2 * N + 1 = p) (hNj : N < j) (hjp : j ≤ p) :
    ‖((betaHarmonic j - (-1 : ℚ) ^ N / (p : ℚ) ^ 4 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  classical
  let F : ℕ → ℚ := fun n => (-1 : ℚ) ^ n / (2 * (n : ℚ) + 1) ^ 4
  have hN : N ∈ Finset.range j := Finset.mem_range.mpr hNj
  have he : betaHarmonic j - (-1 : ℚ) ^ N / (p : ℚ) ^ 4 =
      ∑ n ∈ (Finset.range j).erase N, F n := by
    have hcast : 2 * (N : ℚ) + 1 = p := by exact_mod_cast hNp
    change (∑ n ∈ Finset.range j, F n) - (-1 : ℚ) ^ N / (p : ℚ) ^ 4 = _
    rw [← Finset.sum_erase_add _ F hN]
    dsimp [F]
    rw [hcast]
    ring
  rw [he]
  push_cast
  apply sum_norm_le_one p
  intro n hn
  have hn' := Finset.mem_erase.mp hn
  have hnr := Finset.mem_range.mp hn'.2
  have hunit := nat_unit_norm p (2 * n + 1) (by omega) (by omega) (by omega)
  have hunit' : ‖(2 * (n : ℚ_[p]) + 1)‖ = 1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hunit
  dsimp [F]
  push_cast
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, hunit', div_one, le_refl]

private theorem small_nat_unit_norm (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) : ‖(n : ℚ_[p])‖ = 1 :=
  nat_unit_norm p n hn (by omega) (by omega)

/-- The first exceptional functional value has exactly a first-order pole. -/
theorem poleValue_central_norm (p N : ℕ) [Fact p.Prime]
    (hp : 7 < p) (hNp : 2 * N + 1 = p) :
    ‖(poleValue N 0 : ℚ_[p])‖ = (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpn : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hpR)
  have hcast : 2 * (N : ℚ_[p]) + 1 = p := by exact_mod_cast hNp
  have htwo : ‖(2 : ℚ_[p])‖ = 1 := small_nat_unit_norm p 2 (by norm_num) (by omega)
  have hsix : ‖(6 : ℚ_[p])‖ = 1 := small_nat_unit_norm p 6 (by norm_num) (by omega)
  let A : ℚ_[p] := -(p : ℚ_[p]) ^ 3 * (-1) ^ N * (betaHarmonic N : ℚ_[p]) - 1 / 6
  let B : ℚ_[p] := (-1) ^ N / (2 * (p : ℚ_[p]))
  have hA : ‖A‖ ≤ 1 := by
    apply sub_norm_le_one p
    · rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_pow, norm_neg, norm_one, one_pow, mul_one]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _)
        (Padic.norm_p_lt_one (p := p)).le) (norm_nonneg _)
        (betaHarmonic_below_norm p N N hNp le_rfl)
    · simp only [norm_div, norm_one, hsix, div_self (by norm_num : (1 : ℝ) ≠ 0), le_refl]
  have hB : ‖B‖ = (p : ℝ) := by
    dsimp [B]
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_mul, htwo, one_mul, Padic.norm_p]
    simp
  have he : (poleValue N 0 : ℚ_[p]) = B + A := by
    dsimp [poleValue, A, B]
    push_cast
    rw [hcast]
    ring
  have hne : ‖B‖ ≠ ‖A‖ := by
    rw [hB]
    exact ne_of_gt (hA.trans_lt hpR)
  rw [he, Padic.add_eq_max_of_ne hne, hB, max_eq_left (hA.trans hpR.le)]

/-- Every subsequent odd pole before 2p has exact fourth-order size. -/
theorem poleValue_outer_norm (p N j : ℕ) [Fact p.Prime]
    (hp : 7 < p) (hNp : 2 * N + 1 = p) (hNj : N < j) (hjp : j < p) :
    ‖(poleValue j 0 : ℚ_[p])‖ = (p : ℝ) ^ 4 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpn : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have htwo : ‖(2 : ℚ_[p])‖ = 1 := small_nat_unit_norm p 2 (by norm_num) (by omega)
  have hsix : ‖(6 : ℚ_[p])‖ = 1 := small_nat_unit_norm p 6 (by norm_num) (by omega)
  let a : ℚ_[p] := 2 * (j : ℚ_[p]) + 1
  let E : ℚ_[p] := ((betaHarmonic j - (-1 : ℚ) ^ N / (p : ℚ) ^ 4 : ℚ) : ℚ_[p])
  have ha : ‖a‖ = 1 := by
    have h := nat_unit_norm p (2 * j + 1) (by omega) (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, a] using h
  have hE : ‖E‖ ≤ 1 := betaHarmonic_regular_norm p N j hNp hNj hjp.le
  let A : ℚ_[p] := -a ^ 3 * (-1) ^ j * E - 1 / 6 + (-1) ^ j / (2 * a)
  let B : ℚ_[p] := -a ^ 3 * (-1) ^ j * (-1) ^ N / (p : ℚ_[p]) ^ 4
  have hA : ‖A‖ ≤ 1 := by
    apply add_norm_le_one p
    · apply sub_norm_le_one p
      · simpa only [norm_mul, norm_pow, norm_neg, norm_one, ha,
          one_pow, one_mul] using hE
      · simp only [norm_div, norm_one, hsix, div_self (by norm_num : (1 : ℝ) ≠ 0), le_refl]
    · simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, ha, htwo,
        one_pow, one_mul, div_self (by norm_num : (1 : ℝ) ≠ 0), le_refl]
  have hB : ‖B‖ = (p : ℝ) ^ 4 := by
    dsimp [B]
    rw [norm_div, norm_mul, norm_mul, norm_neg, norm_pow, norm_pow, norm_pow,
      norm_pow, norm_neg, norm_one, norm_neg, norm_one, ha, Padic.norm_p]
    simp
  have he : (poleValue j 0 : ℚ_[p]) = B + A := by
    dsimp [poleValue, A, B, E, a]
    push_cast
    ring
  have hlarge : (1 : ℝ) < (p : ℝ) ^ 4 := one_lt_pow₀ hpR (by norm_num)
  have hne : ‖B‖ ≠ ‖A‖ := by
    rw [hB]
    exact ne_of_gt (hA.trans_lt hlarge)
  rw [he, Padic.add_eq_max_of_ne hne, hB, max_eq_left (hA.trans hlarge.le)]

end ManuscriptChain.BetaOddPoleNorm

#print axioms ManuscriptChain.BetaOddPoleNorm.betaHarmonic_below_norm
#print axioms ManuscriptChain.BetaOddPoleNorm.betaHarmonic_regular_norm
#print axioms ManuscriptChain.BetaOddPoleNorm.poleValue_central_norm
#print axioms ManuscriptChain.BetaOddPoleNorm.poleValue_outer_norm
