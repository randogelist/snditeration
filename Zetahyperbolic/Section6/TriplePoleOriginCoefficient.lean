import Zetahyperbolic.Section6.TriplePoleGeneralCancellation

/-! The exact first nonzero Taylor coefficient of the literal printed family. -/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace ManuscriptChain.TriplePoleCancellation

theorem denominatorTail_zero (n : ℕ) :
    denominatorTail n 0 = ((6*n).factorial : ℝ)^3 := by
  unfold denominatorTail
  simp only [zero_add, Finset.prod_pow]
  congr 1
  exact_mod_cast Finset.prod_range_add_one_eq_factorial (6*n)

theorem numeratorTail_succ_zero (n : ℕ) :
    numeratorTail (n+1) 0 = (n.factorial : ℝ)^6 := by
  induction n with
  | zero => norm_num [numeratorTail]
  | succ n ih =>
    have hs : (Finset.Icc 1 (n+1+1)).erase 1 =
        insert (n+2) ((Finset.Icc 1 (n+1)).erase 1) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert]
      omega
    have hn : n+2 ∉ (Finset.Icc 1 (n+1)).erase 1 := by
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    change (∏ j ∈ (Finset.Icc 1 (n+1+1)).erase 1,
      ((0 : ℝ) - (j : ℝ) + 1)^6) = _
    rw [hs, Finset.prod_insert hn]
    change ((0 : ℝ) - ((n+2 : ℕ) : ℝ) + 1)^6 * numeratorTail (n+1) 0 = _
    rw [ih, Nat.factorial_succ]
    push_cast
    ring

theorem regularFactor_succ_zero (n : ℕ) :
    regularFactor (n+1) 0 = (n.factorial : ℝ)^6 := by
  unfold regularFactor
  rw [numeratorTail_succ_zero, denominatorTail_zero]
  have h : (((6*(n+1)).factorial : ℝ)^3) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast Nat.factorial_ne_zero (6*(n+1))
  field_simp [h]

/-- The coefficient of t³, rather than t⁻³, is exactly ((n-1)!)⁶.
The successor parameter avoids truncated subtraction. -/
theorem printedR_succ_div_cube_tendsto (n : ℕ) :
    Tendsto (fun t : ℝ => printedR (n+1) t / t^3) (𝓝[≠] 0)
      (𝓝 ((n.factorial : ℝ)^6)) := by
  simpa only [regularFactor_succ_zero] using
    printedR_div_cube_tendsto (n+1) (by omega)

end ManuscriptChain.TriplePoleCancellation
