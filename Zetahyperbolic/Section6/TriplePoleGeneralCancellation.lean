import Zetahyperbolic.Section6.TriplePoleCancellation

/-!
# The origin is a cubic zero for every positive member of the printed family

This extends the n=1 counterexample by factoring the literal finite products,
for every n≥1. The residual factor is continuous and nonzero at zero. Thus the
origin is a zero of order three, not a triple pole. No valuation conclusion is
deduced from this repair.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace ManuscriptChain.TriplePoleCancellation

def numeratorTail (n : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ (Finset.Icc 1 n).erase 1, (t - (j : ℝ) + 1)^6

def denominatorTail (n : ℕ) (t : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (6*n), (t + ((k+1 : ℕ) : ℝ))^3

def regularFactor (n : ℕ) (t : ℝ) : ℝ :=
  ((6*n).factorial : ℝ)^3 * numeratorTail n t / denominatorTail n t

theorem numerator_factor (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (∏ j ∈ Finset.Icc 1 n, (t - (j : ℝ) + 1)^6) =
      t^6 * numeratorTail n t := by
  have h := Finset.mul_prod_erase (Finset.Icc 1 n)
    (fun j : ℕ => (t - (j : ℝ) + 1)^6) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  simpa only [Nat.cast_one, sub_add_cancel, numeratorTail] using h.symm

theorem denominator_factor (n : ℕ) (t : ℝ) :
    (∏ k ∈ Finset.range (6*n+1), (t + (k : ℝ))^3) =
      denominatorTail n t * t^3 := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, denominatorTail]

/-- Equality holds even at zero, using Mathlib's total field division. -/
theorem printedR_eq_cubic (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    printedR n t = t^3 * regularFactor n t := by
  unfold printedR regularFactor
  rw [numerator_factor n hn t, denominator_factor]
  by_cases ht : t = 0
  · simp [ht]
  by_cases hd : denominatorTail n t = 0
  · simp [hd]
  field_simp [ht, hd] <;> ring

theorem denominatorTail_zero_ne (n : ℕ) : denominatorTail n 0 ≠ 0 := by
  unfold denominatorTail
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  apply pow_ne_zero
  simp only [zero_add]
  exact_mod_cast (Nat.succ_ne_zero k)

theorem numeratorTail_zero_ne (n : ℕ) : numeratorTail n 0 ≠ 0 := by
  unfold numeratorTail
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply pow_ne_zero
  have hj1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
  have hjreal : (j : ℝ) ≠ 1 := by exact_mod_cast hj1
  intro h
  apply hjreal
  linarith

theorem regularFactor_zero_ne (n : ℕ) : regularFactor n 0 ≠ 0 := by
  unfold regularFactor
  apply div_ne_zero
  · apply mul_ne_zero
    · apply pow_ne_zero
      exact_mod_cast (Nat.factorial_ne_zero (6*n))
    · exact numeratorTail_zero_ne n
  · exact denominatorTail_zero_ne n

theorem regularFactor_continuousAt_zero (n : ℕ) :
    ContinuousAt (regularFactor n) 0 := by
  unfold regularFactor
  apply ContinuousAt.div
  · unfold numeratorTail
    fun_prop
  · unfold denominatorTail
    fun_prop
  · exact denominatorTail_zero_ne n

/-- The normalized cubic quotient has a nonzero limiting value. -/
theorem printedR_div_cube_tendsto (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun t : ℝ => printedR n t / t^3) (𝓝[≠] 0)
      (𝓝 (regularFactor n 0)) := by
  apply Tendsto.congr' _ ((regularFactor_continuousAt_zero n).tendsto.mono_left
    nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rw [printedR_eq_cubic n hn]
  field_simp [ht0]

/-- For every n≥1 the alleged leading Laurent coefficient is actually zero. -/
theorem actual_leading_zero (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun t : ℝ => t^3 * printedR n t) (𝓝[≠] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun t : ℝ => t^3 * (t^3 * regularFactor n t)) 0 :=
    (continuousAt_id.pow 3).mul
      ((continuousAt_id.pow 3).mul (regularFactor_continuousAt_zero n))
  have h := hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [printedR_eq_cubic n hn, zero_pow (by decide : 3 ≠ 0),
    zero_mul] using h

theorem printedLeading_zero_eq_factorial (n : ℕ) :
    printedLeading n 0 = (n.factorial : ℝ) := by
  simp [printedLeading]

/-- Uniform refutation, rather than only one numerical instance. -/
theorem printed_leading_formula_fails_all (n : ℕ) (hn : 1 ≤ n) :
    ¬ Tendsto (fun t : ℝ => t^3 * printedR n t) (𝓝[≠] 0)
      (𝓝 (printedLeading n 0)) := by
  intro h
  have hz := tendsto_nhds_unique (actual_leading_zero n hn) h
  rw [printedLeading_zero_eq_factorial] at hz
  have hnz : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact hnz hz.symm

end ManuscriptChain.TriplePoleCancellation
