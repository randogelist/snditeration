import Zetahyperbolic.Section6.OuterHarmonicBound
import Zetahyperbolic.Section6.OuterPrimeLocalBlock
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# Actual local block at every p-adic integral evaluation

The coefficients are the actual rational Beukers moments, embedded in Q_p.
For every X of norm at most one the local determinant has norm p^14, and
every integral primitive coefficient vector retains an output of norm p^7.
This is the corrected primitive-vector version of manuscript 6.1(3).
-/
noncomputable section
open scoped Matrix BigOperators

namespace ManuscriptChain.Beukers

private lemma rational_norm_le_one_of_valuation_nonneg (p : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : 0 ≤ padicValRat p q) : ‖(q : ℚ_[p])‖ ≤ 1 := by
  by_cases hn : q = 0
  · simp [hn]
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hn]
  exact_mod_cast (zpow_le_one_of_nonpos₀
    (show (1 : ℚ) ≤ p by exact_mod_cast (Fact.out : p.Prime).one_le)
    (neg_nonpos.mpr hq))

private lemma rational_norm_seven (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : padicValRat p q = -7) : ‖(q : ℚ_[p])‖ = (p : ℝ)^7 := by
  have hn : q ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hq
    norm_num at hq
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hn, hq]
  norm_num

private lemma norm_add_eq_left_of_lt (p : ℕ) [Fact p.Prime]
    (a b : ℚ_[p]) (h : ‖b‖ < ‖a‖) : ‖a+b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne (ne_of_gt h), max_eq_left h.le]

def padicLocalMatrix (p : ℕ) [Fact p.Prime] (r : ℕ) (X : ℚ_[p]) :
    Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![X - (Real.harmonic 7 r : ℚ_[p]), (Real.dualConstant 7 r (r+p) : ℚ_[p]);
    (Real.dualConstant 7 r (r+p) : ℚ_[p]), X - (Real.harmonic 7 (r+p) : ℚ_[p])]

theorem padicLocalMatrix_low_norm (p r : ℕ) [Fact p.Prime]
    (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ‖X - (Real.harmonic 7 r : ℚ_[p])‖ ≤ 1 := by
  have hh := rational_norm_le_one_of_valuation_nonneg p (Real.harmonic 7 r)
    (harmonic_below_prime_valuation_nonneg p 7 r hr)
  simpa only [sub_eq_add_neg] using
    (Padic.nonarchimedean X (-(Real.harmonic 7 r : ℚ_[p]))).trans
      (max_le hX (by simpa only [norm_neg] using hh))

theorem padicLocalMatrix_offdiagonal_norm (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) :
    ‖(Real.dualConstant 7 r (r+p) : ℚ_[p])‖ = (p : ℝ)^7 :=
  rational_norm_seven p _ (dualConstant_outer_valuation p r hp11 hr)

theorem padicLocalMatrix_high_norm (p r : ℕ) [Fact p.Prime]
    (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ‖X - (Real.harmonic 7 (r+p) : ℚ_[p])‖ = (p : ℝ)^7 := by
  let D : ℚ := Real.harmonic 7 (r+p) - Real.harmonic 7 r
  have hD : ‖(D : ℚ_[p])‖ = (p : ℝ)^7 := rational_norm_seven p D
    (harmonic_difference_outer_valuation p r 7 hr (by norm_num))
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlarge : (1 : ℝ) < (p : ℝ)^7 := one_lt_pow₀ hp (by norm_num)
  have hlow := padicLocalMatrix_low_norm p r hr X hX
  have he : X - (Real.harmonic 7 (r+p) : ℚ_[p]) =
      -(D : ℚ_[p]) + (X - (Real.harmonic 7 r : ℚ_[p])) := by
    dsimp [D]
    push_cast
    ring
  rw [he, norm_add_eq_left_of_lt p, norm_neg, hD]
  simpa only [norm_neg, hD] using hlow.trans_lt hlarge

/-- Every p-integral evaluation of the actual block has two exact
seventh-order determinant poles. -/
theorem padicLocalMatrix_det_norm (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ‖(padicLocalMatrix p r X).det‖ = (p : ℝ)^14 := by
  let a := X - (Real.harmonic 7 r : ℚ_[p])
  let b := (Real.dualConstant 7 r (r+p) : ℚ_[p])
  let d := X - (Real.harmonic 7 (r+p) : ℚ_[p])
  have ha : ‖a‖ ≤ 1 := padicLocalMatrix_low_norm p r hr X hX
  have hb : ‖b‖ = (p : ℝ)^7 := padicLocalMatrix_offdiagonal_norm p r hp11 hr
  have hd : ‖d‖ = (p : ℝ)^7 := padicLocalMatrix_high_norm p r hr X hX
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hprod : ‖a*d‖ ≤ (p : ℝ)^7 := by
    rw [norm_mul, hd]
    simpa using mul_le_mul_of_nonneg_right ha (by positivity : (0 : ℝ) ≤ (p : ℝ)^7)
  have hsquare : ‖-(b^2)‖ = (p : ℝ)^14 := by
    rw [norm_neg, norm_pow, hb]
    ring
  have he : (padicLocalMatrix p r X).det = -(b^2) + a*d := by
    simp [padicLocalMatrix, Matrix.det_fin_two, a, b, d, pow_two]
    ring
  rw [he, norm_add_eq_left_of_lt p, hsquare]
  rw [hsquare]
  exact hprod.trans_lt (pow_lt_pow_right₀ hp (by norm_num))

private theorem padicLocalMatrix_row0_of_second_unit (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1)
    (c : Fin 2 → ℚ_[p]) (hc0 : ‖c 0‖ ≤ 1) (hc1 : ‖c 1‖ = 1) :
    ‖(padicLocalMatrix p r X).mulVec c 0‖ = (p : ℝ)^7 := by
  let a := X - (Real.harmonic 7 r : ℚ_[p])
  let b := (Real.dualConstant 7 r (r+p) : ℚ_[p])
  have ha : ‖a‖ ≤ 1 := padicLocalMatrix_low_norm p r hr X hX
  have hb : ‖b‖ = (p : ℝ)^7 := padicLocalMatrix_offdiagonal_norm p r hp11 hr
  have hprod : ‖b*c 1‖ = (p : ℝ)^7 := by rw [norm_mul, hb, hc1, mul_one]
  have hother : ‖a*c 0‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hc0
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have he : (padicLocalMatrix p r X).mulVec c 0 = b*c 1 + a*c 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, padicLocalMatrix, a, b]
    ring
  rw [he, norm_add_eq_left_of_lt p, hprod]
  rw [hprod]
  exact hother.trans_lt (one_lt_pow₀ hp (by norm_num))

/-- Primitive, not merely nonzero, is the correct hypothesis. This statement
covers all p-adic integral evaluations and all p-adic integral vectors. -/
theorem padicLocalMatrix_primitive_pole (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1)
    (c : Fin 2 → ℚ_[p]) (hc : ∀ i, ‖c i‖ ≤ 1)
    (hprimitive : ∃ i, ‖c i‖ = 1) :
    ∃ i, ‖(padicLocalMatrix p r X).mulVec c i‖ = (p : ℝ)^7 := by
  by_cases hsecond : ‖c 1‖ = 1
  · exact ⟨0, padicLocalMatrix_row0_of_second_unit p r hp11 hr X hX c (hc 0) hsecond⟩
  have hfirst : ‖c 0‖ = 1 := by
    obtain ⟨i, hi⟩ := hprimitive
    fin_cases i
    · exact hi
    · exact False.elim (hsecond hi)
  refine ⟨1, ?_⟩
  let b := (Real.dualConstant 7 r (r+p) : ℚ_[p])
  let d := X - (Real.harmonic 7 (r+p) : ℚ_[p])
  have hb : ‖b‖ = (p : ℝ)^7 := padicLocalMatrix_offdiagonal_norm p r hp11 hr
  have hd : ‖d‖ = (p : ℝ)^7 := padicLocalMatrix_high_norm p r hr X hX
  have hprod : ‖b*c 0‖ = (p : ℝ)^7 := by rw [norm_mul, hb, hfirst, mul_one]
  have hother : ‖d*c 1‖ < (p : ℝ)^7 := by
    rw [norm_mul, hd]
    have hp : (0 : ℝ) < (p : ℝ)^7 := by
      exact pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
    simpa using mul_lt_mul_of_pos_left (lt_of_le_of_ne (hc 1) hsecond) hp
  have he : (padicLocalMatrix p r X).mulVec c 1 = b*c 0 + d*c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, padicLocalMatrix, b, d]
  rw [he, norm_add_eq_left_of_lt p, hprod]
  simpa only [hprod] using hother

/-- The literal nonzero-vector assertion fails for the actual moment block:
the nonzero integral vector (p,0) lowers both output poles to order at most six. -/
theorem padicLocalMatrix_nonzero_vector_cancellation (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ_[p]) (hX : ‖X‖ ≤ 1) :
    ∃ c : Fin 2 → ℚ_[p], c ≠ 0 ∧ (∀ i, ‖c i‖ ≤ 1) ∧
      (∀ i, ‖(padicLocalMatrix p r X).mulVec c i‖ ≤ (p : ℝ)^6) ∧
      ‖(padicLocalMatrix p r X).mulVec c 1‖ = (p : ℝ)^6 := by
  let c : Fin 2 → ℚ_[p] := ![(p : ℚ_[p]), 0]
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpn : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have h0 : ‖(padicLocalMatrix p r X).mulVec c 0‖ ≤ (p : ℝ)^6 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, padicLocalMatrix, c,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      mul_zero, add_zero]
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖(p : ℚ_[p])‖ := mul_le_mul_of_nonneg_right
        (padicLocalMatrix_low_norm p r hr X hX) (norm_nonneg _)
      _ ≤ 1 := by simpa using (Padic.norm_p_lt_one (p := p)).le
      _ ≤ (p : ℝ)^6 := one_le_pow₀ hp.le
  have h1 : ‖(padicLocalMatrix p r X).mulVec c 1‖ = (p : ℝ)^6 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, padicLocalMatrix, c,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      mul_zero, add_zero]
    change ‖(Real.dualConstant 7 r (r+p) : ℚ_[p]) * (p : ℚ_[p])‖ = (p : ℝ)^6
    rw [norm_mul, padicLocalMatrix_offdiagonal_norm p r hp11 hr, Padic.norm_p]
    field_simp [hpn]
    <;> ring
  refine ⟨c, ?_, ?_, ?_, h1⟩
  · intro hz
    have he : (p : ℚ_[p]) = 0 := congrFun hz 0
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he
  · intro i
    fin_cases i
    · simpa [c] using (Padic.norm_p_lt_one (p := p)).le
    · simp [c]
  · intro i
    fin_cases i
    · exact h0
    · exact h1.le

end ManuscriptChain.Beukers
