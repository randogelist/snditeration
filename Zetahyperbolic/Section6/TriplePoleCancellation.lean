import Mathlib

/-!
# A cancelled pole in the printed triple-pole family (Theorem 6.9)

The functions below transcribe the displayed manuscript formulas. At n=1,
its numerator has a sixth-order zero at t=0 whereas the denominator has
only a third-order zero. Thus the coefficient of the alleged t^(-3) term
is zero, contrary to the displayed C_(1,0)^(3)=1. This refutes that coefficient
formula only; it does not refute or prove the remaining valuation assertions.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace ManuscriptChain.TriplePoleCancellation

/-- The actual rational function displayed in manuscript Theorem 6.9(1). -/
def printedR (n : ℕ) (t : ℝ) : ℝ :=
  ((6 * n).factorial : ℝ) ^ 3 *
    (∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ) + 1) ^ 6) /
      ∏ k ∈ Finset.range (6 * n + 1), (t + (k : ℝ)) ^ 3

/-- The printed proposed leading Laurent coefficient, with both indices explicit. -/
def printedLeading (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (Nat.choose (6 * n) k : ℝ) ^ 3 *
    (Nat.choose (n + k) k : ℝ) ^ 6 * (n.factorial : ℝ)

/-- The denominator after removal of its k=0 factor, at n=1. -/
def tailOne (t : ℝ) : ℝ :=
  (t + 1) ^ 3 * (t + 2) ^ 3 * (t + 3) ^ 3 *
    (t + 4) ^ 3 * (t + 5) ^ 3 * (t + 6) ^ 3

/-- Direct expansion of the actual n=1 finite products. -/
theorem printedR_one (t : ℝ) :
    printedR 1 t = (720 : ℝ) ^ 3 * t ^ 6 / (t ^ 3 * tailOne t) := by
  norm_num [printedR, tailOne, Finset.prod_range_succ] <;> congr 1 <;> ring

/-- Cancellation computed before taking a limit. Field division is total,
so the identity also holds at the cancelled pole itself. -/
theorem scaled_printedR_one (t : ℝ) :
    t ^ 3 * printedR 1 t = (720 : ℝ) ^ 3 * t ^ 6 / tailOne t := by
  rw [printedR_one]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hd : tailOne t = 0
  · simp [hd]
  field_simp [ht, hd] <;> ring

/-- The actual scaled rational function has limiting value zero at the origin. -/
theorem scaled_printedR_one_tendsto_zero :
    Tendsto (fun t : ℝ => t ^ 3 * printedR 1 t) (𝓝 0) (𝓝 0) := by
  have hd : tailOne (0 : ℝ) ≠ 0 := by norm_num [tailOne]
  have hc : ContinuousAt (fun t : ℝ => (720 : ℝ) ^ 3 * t ^ 6 / tailOne t) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · unfold tailOne
      fun_prop
    · exact hd
  simpa [scaled_printedR_one] using hc.tendsto

/-- The punctured limit used to recover the t^(-3) Laurent coefficient. -/
theorem actual_leading_one_zero :
    Tendsto (fun t : ℝ => t ^ 3 * printedR 1 t) (𝓝[≠] 0) (𝓝 0) :=
  scaled_printedR_one_tendsto_zero.mono_left nhdsWithin_le_nhds

theorem printed_leading_one_zero : printedLeading 1 0 = 1 := by
  norm_num [printedLeading]

/-- The manuscript's proposed leading coefficient is not the actual limit. -/
theorem printed_leading_formula_fails :
    ¬ Tendsto (fun t : ℝ => t ^ 3 * printedR 1 t) (𝓝[≠] 0)
      (𝓝 (printedLeading 1 0)) := by
  intro h
  have hzero : (0 : ℝ) = printedLeading 1 0 :=
    tendsto_nhds_unique actual_leading_one_zero h
  rw [printed_leading_one_zero] at hzero
  exact zero_ne_one hzero

end ManuscriptChain.TriplePoleCancellation
