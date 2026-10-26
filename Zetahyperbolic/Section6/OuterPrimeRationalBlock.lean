import Zetahyperbolic.Section6.BeukersOuterValuation
import Zetahyperbolic.Section6.OuterHarmonicBound
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The actual rational local moment block

At every p-integral rational X, the 2-by-2 block indexed by r,r+p has
determinant valuation exactly -14. Its leading off-diagonal square cannot
cancel the product of the diagonal entries, whose valuation is at least -7.
This result is over rational evaluations; it does not silently replace the
all-p-adic-evaluations statement of the manuscript.
-/

noncomputable section
open scoped Matrix BigOperators

namespace ManuscriptChain.Beukers

private lemma valuation_add_eq_left (p : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : a ≠ 0) (hlt : padicValRat p a < padicValRat p b) :
    padicValRat p (a+b) = padicValRat p a := by
  by_cases hb : b = 0
  · simp [hb]
  · have hab : a+b ≠ 0 := by
      intro hz
      have he : a = -b := by linarith
      rw [he, padicValRat.neg] at hlt
      exact lt_irrefl _ hlt
    exact padicValRat.add_eq_of_lt hab ha hb hlt

private lemma valuation_nonneg_sub (p : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a-b) := by
  by_cases h : a-b = 0
  · simp [h]
  · have hm := padicValRat.min_le_padicValRat_add (p := p)
      (q := a) (r := -b) (by simpa [sub_eq_add_neg] using h)
    rw [padicValRat.neg] at hm
    exact le_trans (le_min ha hb) (by simpa [sub_eq_add_neg] using hm)

def rationalLocalMatrix (p r : ℕ) (X : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![X - Real.harmonic 7 r, Real.dualConstant 7 r (r+p);
    Real.dualConstant 7 r (r+p), X - Real.harmonic 7 (r+p)]

theorem rationalLocalMatrix_low_diagonal (p r : ℕ) [Fact p.Prime]
    (hr : r < p) (X : ℚ) (hX : 0 ≤ padicValRat p X) :
    0 ≤ padicValRat p (X - Real.harmonic 7 r) :=
  valuation_nonneg_sub p X _ hX (harmonic_below_prime_valuation_nonneg p 7 r hr)

theorem rationalLocalMatrix_high_diagonal (p r : ℕ) [Fact p.Prime]
    (hr : r < p) (X : ℚ) (hX : 0 ≤ padicValRat p X) :
    padicValRat p (X - Real.harmonic 7 (r+p)) = -7 := by
  let D := Real.harmonic 7 (r+p) - Real.harmonic 7 r
  have hD : padicValRat p D = -7 :=
    harmonic_difference_outer_valuation p r 7 hr (by norm_num)
  have hDn : -D ≠ 0 := by
    intro hz
    have he : D = 0 := neg_eq_zero.mp hz
    rw [he, padicValRat.zero] at hD
    norm_num at hD
  have hlow := rationalLocalMatrix_low_diagonal p r hr X hX
  have he : X - Real.harmonic 7 (r+p) = -D + (X-Real.harmonic 7 r) := by
    dsimp [D]
    ring
  rw [he, valuation_add_eq_left p _ _ hDn, padicValRat.neg, hD]
  rw [padicValRat.neg, hD]
  omega

/-- The actual local block has a determinant with two full seventh-order
poles. No determinant valuation is supplied as a hypothesis. -/
theorem rationalLocalMatrix_det_valuation (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ) (hX : 0 ≤ padicValRat p X) :
    padicValRat p (rationalLocalMatrix p r X).det = -14 := by
  let a := X - Real.harmonic 7 r
  let b := Real.dualConstant 7 r (r+p)
  let d := X - Real.harmonic 7 (r+p)
  have ha : 0 ≤ padicValRat p a := rationalLocalMatrix_low_diagonal p r hr X hX
  have hb : padicValRat p b = -7 := dualConstant_outer_valuation p r hp11 hr
  have hd : padicValRat p d = -7 := rationalLocalMatrix_high_diagonal p r hr X hX
  have hbn : b ≠ 0 := by
    intro he
    rw [he, padicValRat.zero] at hb
    norm_num at hb
  have hdn : d ≠ 0 := by
    intro he
    rw [he, padicValRat.zero] at hd
    norm_num at hd
  have hprod : -7 ≤ padicValRat p (a*d) := by
    by_cases han : a = 0
    · simp [han]
    · rw [padicValRat.mul han hdn, hd]
      omega
  have hsquare : padicValRat p (-(b^2)) = -14 := by
    rw [padicValRat.neg, padicValRat.pow, hb]
    norm_num
  have he : (rationalLocalMatrix p r X).det = -(b^2) + a*d := by
    simp [rationalLocalMatrix, Matrix.det_fin_two, a, b, d, pow_two]
    ring
  rw [he, valuation_add_eq_left p _ _ (neg_ne_zero.mpr (pow_ne_zero _ hbn)), hsquare]
  rw [hsquare]
  omega

theorem rationalLocalMatrix_det_ne_zero (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ) (hX : 0 ≤ padicValRat p X) :
    (rationalLocalMatrix p r X).det ≠ 0 := by
  intro hz
  have h := rationalLocalMatrix_det_valuation p r hp11 hr X hX
  rw [hz, padicValRat.zero] at h
  norm_num at h

private lemma valuation_nonneg_mul (p : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    0 ≤ padicValRat p (a*b) := by
  by_cases han : a = 0
  · simp [han]
  by_cases hbn : b = 0
  · simp [hbn]
  rw [padicValRat.mul han hbn]
  exact add_nonneg ha hb

private lemma first_row_of_second_unit (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ) (hX : 0 ≤ padicValRat p X)
    (c : Fin 2 → ℚ) (hc0 : 0 ≤ padicValRat p (c 0))
    (hc1n : c 1 ≠ 0) (hc1 : padicValRat p (c 1) = 0) :
    padicValRat p ((rationalLocalMatrix p r X).mulVec c 0) = -7 := by
  let a := X - Real.harmonic 7 r
  let b := Real.dualConstant 7 r (r+p)
  have ha : 0 ≤ padicValRat p a := rationalLocalMatrix_low_diagonal p r hr X hX
  have hb : padicValRat p b = -7 := dualConstant_outer_valuation p r hp11 hr
  have hbn : b ≠ 0 := by
    intro he
    rw [he, padicValRat.zero] at hb
    norm_num at hb
  have hprod : padicValRat p (b*c 1) = -7 := by
    rw [padicValRat.mul hbn hc1n, hb, hc1]
    norm_num
  have hother := valuation_nonneg_mul p a (c 0) ha hc0
  have he : (rationalLocalMatrix p r X).mulVec c 0 = b*c 1 + a*c 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rationalLocalMatrix, a, b]
    ring
  rw [he, valuation_add_eq_left p _ _ (mul_ne_zero hbn hc1n), hprod]
  rw [hprod]
  omega

/-- Corrected rational local obstruction: a p-integral primitive coefficient
vector retains an exact seventh-order pole in at least one output row. -/
theorem rationalLocalMatrix_primitive_pole (p r : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hr : r < p) (X : ℚ) (hX : 0 ≤ padicValRat p X)
    (c : Fin 2 → ℚ) (hc : ∀ i, 0 ≤ padicValRat p (c i))
    (hprimitive : ∃ i, c i ≠ 0 ∧ padicValRat p (c i) = 0) :
    ∃ i, padicValRat p ((rationalLocalMatrix p r X).mulVec c i) = -7 := by
  by_cases hsecond : c 1 ≠ 0 ∧ padicValRat p (c 1) = 0
  · exact ⟨0, first_row_of_second_unit p r hp11 hr X hX c (hc 0)
      hsecond.1 hsecond.2⟩
  have hfirst : c 0 ≠ 0 ∧ padicValRat p (c 0) = 0 := by
    obtain ⟨i, hi⟩ := hprimitive
    fin_cases i
    · exact hi
    · exact False.elim (hsecond hi)
  refine ⟨1, ?_⟩
  let b := Real.dualConstant 7 r (r+p)
  let d := X - Real.harmonic 7 (r+p)
  have hb : padicValRat p b = -7 := dualConstant_outer_valuation p r hp11 hr
  have hd : padicValRat p d = -7 := rationalLocalMatrix_high_diagonal p r hr X hX
  have hbn : b ≠ 0 := by
    intro he
    rw [he, padicValRat.zero] at hb
    norm_num at hb
  have hdn : d ≠ 0 := by
    intro he
    rw [he, padicValRat.zero] at hd
    norm_num at hd
  have hprod : padicValRat p (b*c 0) = -7 := by
    rw [padicValRat.mul hbn hfirst.1, hb, hfirst.2]
    norm_num
  have hother : -7 < padicValRat p (d*c 1) := by
    by_cases hn : c 1 = 0
    · simp [hn]
    have hp : 0 < padicValRat p (c 1) := by
      have hnonneg := hc 1
      have hne : padicValRat p (c 1) ≠ 0 := fun he => hsecond ⟨hn, he⟩
      omega
    rw [padicValRat.mul hdn hn, hd]
    omega
  have he : (rationalLocalMatrix p r X).mulVec c 1 = b*c 0 + d*c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rationalLocalMatrix, b, d]
  rw [he, valuation_add_eq_left p _ _ (mul_ne_zero hbn hfirst.1), hprod]
  simpa [hprod] using hother

end ManuscriptChain.Beukers
