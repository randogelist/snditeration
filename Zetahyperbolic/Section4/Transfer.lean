import Mathlib

/-!
# Section 4: conditional rational-approximation transfer

Proof source adapted from the archived Lean 4.33 file implementing
the integer-polynomial denominator squeeze of manuscript Theorem 4.1.
The local comparison, decay and index-selection inputs are explicit:
this module does not prove the paper's asymptotic analytic estimates.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.RealTransfer

def evalReal (P : Polynomial ℤ) (x : ℝ) : ℝ :=
  (P.map (algebraMap ℤ ℝ)).eval x

theorem polynomial_integer_squeeze (P : Polynomial ℤ) (a : ℤ) (b : ℕ)
    (hb : 0 < b)
    (hne : evalReal P ((a : ℝ) / b) ≠ 0)
    (hsmall : (b : ℝ) ^ P.natDegree * |evalReal P ((a : ℝ) / b)| < 1) :
    False := by
  have hlow := one_le_pow_mul_abs_eval_div
    (K := ℝ) (f := P) (a := a) (b := (b : ℤ))
    (by exact_mod_cast hb) (by simpa [evalReal] using hne)
  have hlow' : (1 : ℝ) ≤ (b : ℝ) ^ P.natDegree *
      |evalReal P ((a : ℝ) / b)| := by
    simpa [evalReal] using hlow
  exact (not_lt_of_ge hlow') hsmall

structure LocalComparison (Q : ℕ → Polynomial ℤ) (ξ : ℝ)
    (radius : ℕ → ℝ) (n₀ : ℕ) : Prop where
  compare : ∀ n, n₀ ≤ n → ∀ x : ℝ,
    |x - ξ| ≤ radius n → evalReal (Q n) ξ ≠ 0 →
    evalReal (Q n) x ≠ 0 ∧
      |evalReal (Q n) x| ≤ 2 * |evalReal (Q n) ξ|

structure Decay (Q : ℕ → Polynomial ℤ) (ξ : ℝ)
    (budget : ℕ → ℝ) (n₀ : ℕ) : Prop where
  nonzero : ∀ n, n₀ ≤ n → evalReal (Q n) ξ ≠ 0
  upper : ∀ n, n₀ ≤ n → |evalReal (Q n) ξ| ≤ budget n

structure IndexBudget (Q : ℕ → Polynomial ℤ) (radius budget : ℕ → ℝ)
    (n₀ μ b₀ : ℕ) : Prop where
  choose : ∀ b : ℕ, 0 < b → b₀ ≤ b →
    ∃ n : ℕ, n₀ ≤ n ∧
      1 / (b : ℝ) ^ μ ≤ radius n ∧
      2 * (b : ℝ) ^ (Q n).natDegree * budget n < 1

def RationalMeasure (ξ : ℝ) (μ b₀ : ℕ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → b₀ ≤ b →
    1 / (b : ℝ) ^ μ < |ξ - (a : ℝ) / b|

theorem conditional_measure
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {radius budget : ℕ → ℝ}
    {n₀ μ b₀ : ℕ}
    (comparison : LocalComparison Q ξ radius n₀)
    (decay : Decay Q ξ budget n₀)
    (index : IndexBudget Q radius budget n₀ μ b₀) :
    RationalMeasure ξ μ b₀ := by
  intro a b hb hbb
  by_contra hnot
  have hclose : |ξ - (a : ℝ) / b| ≤ 1 / (b : ℝ) ^ μ := le_of_not_gt hnot
  obtain ⟨n, hn, hradius, hbudget⟩ := index.choose b hb hbb
  have hclose' : |(a : ℝ) / b - ξ| ≤ radius n := by
    rw [abs_sub_comm]
    exact hclose.trans hradius
  obtain ⟨hne, hcomp⟩ := comparison.compare n hn ((a : ℝ) / b) hclose'
    (decay.nonzero n hn)
  have hbpow : 0 ≤ (b : ℝ) ^ (Q n).natDegree := by positivity
  apply polynomial_integer_squeeze (Q n) a b hb hne
  calc
    (b : ℝ) ^ (Q n).natDegree * |evalReal (Q n) ((a : ℝ) / b)|
        ≤ (b : ℝ) ^ (Q n).natDegree * (2 * |evalReal (Q n) ξ|) :=
      mul_le_mul_of_nonneg_left hcomp hbpow
    _ ≤ (b : ℝ) ^ (Q n).natDegree * (2 * budget n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (decay.upper n hn) (by norm_num)) hbpow
    _ = 2 * (b : ℝ) ^ (Q n).natDegree * budget n := by ring
    _ < 1 := hbudget

theorem RationalMeasure.irrational {ξ : ℝ} {μ b₀ : ℕ}
    (h : RationalMeasure ξ μ b₀) : Irrational ξ := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  let t : ℕ := b₀ + 1
  let b : ℕ := r.den * t
  let a : ℤ := r.num * (t : ℤ)
  have ht : 0 < t := by dsimp [t]; omega
  have hd : 0 < r.den := r.pos
  have hb : 0 < b := Nat.mul_pos hd ht
  have hbb : b₀ ≤ b := by
    dsimp [b, t]
    nlinarith
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hdR : (r.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hab : (a : ℝ) / (b : ℝ) = ξ := by
    calc
      (a : ℝ) / (b : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
        dsimp [a, b]
        push_cast
        field_simp
      _ = (r : ℝ) := (Rat.cast_def r).symm
      _ = ξ := hr
  have hmeasure := h a b hb hbb
  rw [hab, sub_self, abs_zero] at hmeasure
  have hpositive : (0 : ℝ) < 1 / (b : ℝ) ^ μ := by positivity
  exact (not_lt_of_ge (le_of_lt hpositive)) hmeasure

theorem conditional_irrational
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {radius budget : ℕ → ℝ}
    {n₀ μ b₀ : ℕ}
    (comparison : LocalComparison Q ξ radius n₀)
    (decay : Decay Q ξ budget n₀)
    (index : IndexBudget Q radius budget n₀ μ b₀) :
    Irrational ξ :=
  (conditional_measure comparison decay index).irrational

theorem paper_parameter_inequalities :
    (9 / 10 : ℚ) / (1 / 2500) < 2251 ∧
    (11411 / 1000 : ℚ) * 2251 < 25687 := by norm_num

end ManuscriptChain.RealTransfer
