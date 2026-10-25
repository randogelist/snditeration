import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Tactic

/-!
# Proposition 4.3: the ultrametric zero-free disk

An integer polynomial is nonexpanding on the closed unit ball of every
ultrametric normed field. Consequently its norm is constant on the open ball
about `x` of radius `‖Q(x)‖`. This applies in particular to `ℂ_[p]` and a centre
in `ℤ_[p]`; no assumption about algebraic closure is needed for the proof.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.Ultrametric

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

private theorem norm_pow_sub_pow_le (x y : F) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : x ^ (n + 1) - y ^ (n + 1) =
        x ^ n * (x - y) + (x ^ n - y ^ n) * y := by ring
    rw [hid]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hx)
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right ih (norm_nonneg _)).trans
        (mul_le_of_le_one_right (norm_nonneg _) hy)

/-- Every integral polynomial maps the closed unit ball into itself. -/
theorem norm_eval_le_one (Q : ℤ[X]) (x : F) (hx : ‖x‖ ≤ 1) :
    ‖Q.eval₂ (Int.castRingHom F) x‖ ≤ 1 := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hP hQ)
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, norm_mul, norm_pow]
    exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one F a)
      (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hx)

/-- Integral polynomial evaluation is 1-Lipschitz on the closed unit ball. -/
theorem norm_eval_sub_le (Q : ℤ[X]) (x y : F)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖Q.eval₂ (Int.castRingHom F) x - Q.eval₂ (Int.castRingHom F) y‖ ≤ ‖x - y‖ := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.eval₂_add]
    rw [show P.eval₂ (Int.castRingHom F) x + Q.eval₂ (Int.castRingHom F) x -
        (P.eval₂ (Int.castRingHom F) y + Q.eval₂ (Int.castRingHom F) y) =
        (P.eval₂ (Int.castRingHom F) x - P.eval₂ (Int.castRingHom F) y) +
        (Q.eval₂ (Int.castRingHom F) x - Q.eval₂ (Int.castRingHom F) y) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hP hQ)
  | monomial n a =>
    simp only [Polynomial.eval₂_monomial, ← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one F a)).trans
        (norm_pow_sub_pow_le x y hx hy n)

/-- Proposition 4.3 in an arbitrary ultrametric normed field. -/
theorem norm_eval_eq_of_mem_disk (Q : ℤ[X]) (x y : F)
    (hx : ‖x‖ ≤ 1)
    (hclose : ‖y - x‖ < ‖Q.eval₂ (Int.castRingHom F) x‖) :
    ‖Q.eval₂ (Int.castRingHom F) y‖ = ‖Q.eval₂ (Int.castRingHom F) x‖ := by
  have hdist : ‖y - x‖ ≤ 1 := hclose.le.trans (norm_eval_le_one Q x hx)
  have hy : ‖y‖ ≤ 1 := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by congr 1; ring
      _ ≤ max ‖y - x‖ ‖x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le hdist hx
  have hsmall := (norm_eval_sub_le Q y x hy hx).trans_lt hclose
  have h := IsUltrametricDist.norm_eq_of_add_norm_lt_max
    (x := Q.eval₂ (Int.castRingHom F) y) (y := -Q.eval₂ (Int.castRingHom F) x)
    (by simpa only [← sub_eq_add_neg, norm_neg] using hsmall.trans_le
      (le_max_right ‖Q.eval₂ (Int.castRingHom F) y‖ ‖Q.eval₂ (Int.castRingHom F) x‖))
  simpa only [norm_neg] using h

/-- The entire disk is zero-free when its centre value is nonzero. -/
theorem eval_ne_zero_of_mem_disk (Q : ℤ[X]) (x y : F)
    (hx : ‖x‖ ≤ 1) (hvalue : Q.eval₂ (Int.castRingHom F) x ≠ 0)
    (hclose : ‖y - x‖ < ‖Q.eval₂ (Int.castRingHom F) x‖) :
    Q.eval₂ (Int.castRingHom F) y ≠ 0 := by
  intro hz
  have h := norm_eval_eq_of_mem_disk Q x y hx hclose
  rw [hz, norm_zero] at h
  exact hvalue (norm_eq_zero.mp h.symm)

/-- The manuscript's `ℂ_p` disk, including algebraic and completed roots. -/
theorem padicComplex_zero_free_disk (p : ℕ) [Fact p.Prime] (Q : ℤ[X])
    (ξ : ℂ_[p]) (hξ : ‖ξ‖ ≤ 1)
    (hvalue : Q.eval₂ (Int.castRingHom ℂ_[p]) ξ ≠ 0) :
    ∀ α : ℂ_[p], ‖α - ξ‖ < ‖Q.eval₂ (Int.castRingHom ℂ_[p]) ξ‖ →
      ‖Q.eval₂ (Int.castRingHom ℂ_[p]) α‖ = ‖Q.eval₂ (Int.castRingHom ℂ_[p]) ξ‖ ∧
      Q.eval₂ (Int.castRingHom ℂ_[p]) α ≠ 0 := by
  intro α hα
  exact ⟨norm_eval_eq_of_mem_disk Q ξ α hξ hα,
    eval_ne_zero_of_mem_disk Q ξ α hξ hvalue hα⟩

end ManuscriptChain.Ultrametric
