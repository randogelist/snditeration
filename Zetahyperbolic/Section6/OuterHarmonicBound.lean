import Zetahyperbolic.Section6.BeukersOuterValuation

/-!
# Outer-range lower bounds for the actual harmonic numbers

The first clause of Theorem 6.1(2) concerns every harmonic number up to K,
not only the difference occurring in an off-diagonal entry. These finite-sum
bounds include r=0 using Mathlib's convention `padicValRat p 0 = 0`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ManuscriptChain.Beukers

private theorem finite_sum_valuation_lower (p : ℕ) [Fact p.Prime]
    (c : ℤ) (hc : c ≤ 0) (F : ℕ → ℚ) :
    ∀ n : ℕ, (∀ i : ℕ, i < n → c ≤ padicValRat p (F i)) →
      c ≤ padicValRat p (∑ i ∈ Finset.range n, F i) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using hc
  | succ n ih =>
      intro hF
      rw [Finset.sum_range_succ]
      by_cases hz : (∑ i ∈ Finset.range n, F i) + F n = 0
      · rw [hz, padicValRat.zero]
        exact hc
      · exact (le_min (ih (fun i hi => hF i (by omega)))
          (hF n (by omega))).trans (padicValRat.min_le_padicValRat_add hz)

/-- Harmonics below the first p-multiple are p-integral, for every weight. -/
theorem harmonic_below_prime_valuation_nonneg (p s r : ℕ) [Fact p.Prime]
    (hr : r < p) : 0 ≤ padicValRat p (Real.harmonic s r) := by
  unfold Real.harmonic
  apply finite_sum_valuation_lower p 0 le_rfl
  intro i hi
  have hnd : ¬p ∣ i + 1 :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  simp only [one_div, padicValRat.inv, padicValRat.pow,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd,
    Nat.cast_zero, mul_zero, neg_zero, le_refl]

/-- A denominator strictly below 2p has at most one p-factor. -/
theorem reciprocal_outer_valuation_lower (p s n : ℕ) [Fact p.Prime]
    (hn0 : 0 < n) (hn : n < 2 * p) :
    -(s : ℤ) ≤ padicValRat p (1 / (n : ℚ) ^ s) := by
  have hp : p.Prime := Fact.out
  by_cases hnp : n = p
  · subst n
    rw [one_div, padicValRat.self_pow_inv]
  · have hnd : ¬p ∣ n := by
      rintro ⟨k, hk⟩
      have hk2 : k < 2 := by
        apply (Nat.mul_lt_mul_left hp.pos).mp
        rw [← hk]
        omega
      have hk0 : k ≠ 0 := by
        intro hk0
        simp [hk0] at hk
        omega
      have hk1 : k = 1 := by omega
      apply hnp
      simpa [hk1] using hk
    simp only [one_div, padicValRat.inv, padicValRat.pow,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd,
      Nat.cast_zero, mul_zero, neg_zero]
    omega

/-- Every harmonic number in the outer range has valuation at least -s. -/
theorem harmonic_outer_valuation_lower (p s r : ℕ) [Fact p.Prime]
    (hr : r < 2 * p) :
    -(s : ℤ) ≤ padicValRat p (Real.harmonic s r) := by
  unfold Real.harmonic
  apply finite_sum_valuation_lower p (-(s : ℤ)) (by omega)
  intro i hi
  exact reciprocal_outer_valuation_lower p s (i + 1) (by omega) (by omega)

/-- The opening harmonic-number bound in the original Theorem 6.1(2). -/
theorem theorem_6_1_harmonic_bound (p K r : ℕ) [Fact p.Prime]
    (hK : K < 2 * p) (hrK : r ≤ K) :
    -6 ≤ padicValRat p (Real.harmonic 6 r) := by
  simpa using harmonic_outer_valuation_lower p 6 r (by omega)

/-- Full clause 6.1(2): every harmonic lower bound and the exact rational
off-diagonal formula, identified with the actual Beukers moment. The inequality
`K < 2*p` is the manuscript's strict outer-window condition `K/2 < p`.
No arithmetic property of a merely formal moment is substituted here. -/
theorem theorem_6_1_part_two (p K r₁ r₂ : ℕ) [Fact p.Prime]
    (hp11 : 11 ≤ p) (hK : K < 2 * p) (_hpK : p ≤ K)
    (h₁ : r₁ < p) (h₂ : p ≤ r₂) (h₂K : r₂ ≤ K)
    (hcong : Nat.ModEq p r₁ r₂) :
    (∀ r : ℕ, r ≤ K → -6 ≤ padicValRat p (Real.harmonic 6 r)) ∧
    ∃ q : ℚ,
      q = (Real.harmonic 6 r₁ - Real.harmonic 6 r₂) /
        (6 * ((r₁ : ℚ) - (r₂ : ℚ))) ∧
      (∫ z, z.1 ^ r₁ * z.2 ^ r₂ ∂beukersMeasure) = (q : ℝ) ∧
      padicValRat p q = -7 := by
  have hne : r₁ ≠ r₂ := by omega
  refine ⟨fun r hr => theorem_6_1_harmonic_bound p K r hK hr,
    Real.dualConstant 7 r₁ r₂, ?_, ?_,
    theorem_6_1_offdiagonal_valuation p K r₁ r₂ hp11 hK h₁ h₂ h₂K hcong⟩
  · simp only [Real.dualConstant, hne, if_false]
    norm_num
  · rw [integral_beukersMeasure, moment_eq_dualConstant]
    simp only [hne, if_false, add_zero]

private theorem finset_valuation_nonneg (p : ℕ) [Fact p.Prime]
    (S : Finset ℕ) (F : ℕ → ℚ) :
    (∀ i ∈ S, 0 ≤ padicValRat p (F i)) →
      0 ≤ padicValRat p (∑ i ∈ S, F i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert a S ha ih =>
      intro hF
      rw [Finset.sum_insert ha]
      by_cases hz : F a + ∑ i ∈ S, F i = 0
      · rw [hz, padicValRat.zero]
      · exact (le_min (hF a (Finset.mem_insert_self a S))
          (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))).trans
          (padicValRat.min_le_padicValRat_add hz)

/-- Removing the unique p-pole leaves an actual p-integral rational remainder.
This retains the residue information lost by a bare valuation equality. -/
theorem harmonic_outer_regular_valuation_nonneg (p r s : ℕ) [Fact p.Prime]
    (hr : r < p) :
    0 ≤ padicValRat p (Real.harmonic s (r + p) - Real.harmonic s r -
      1 / (p : ℚ) ^ s) := by
  classical
  have hp : p.Prime := Fact.out
  let F : ℕ → ℚ := fun i => 1 / ((r + i + 1 : ℕ) : ℚ) ^ s
  let j : ℕ := p - r - 1
  have hj : j ∈ Finset.range p := by
    apply Finset.mem_range.mpr
    dsimp [j]
    omega
  have hindex : r + j + 1 = p := by dsimp [j]; omega
  have hjterm : F j = 1 / (p : ℚ) ^ s := by
    dsimp [F]
    rw [hindex]
  have hregular : Real.harmonic s (r + p) - Real.harmonic s r -
      1 / (p : ℚ) ^ s = ∑ i ∈ (Finset.range p).erase j, F i := by
    rw [harmonic_difference_eq_shifted_sum]
    change (∑ i ∈ Finset.range p, F i) - 1 / (p : ℚ) ^ s = _
    rw [← Finset.sum_erase_add _ _ hj, hjterm]
    ring
  rw [hregular]
  apply finset_valuation_nonneg
  intro i hi
  have hir : i < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
  have hij : i ≠ j := Finset.ne_of_mem_erase hi
  have hne : r + i + 1 ≠ p := by
    intro he
    apply hij
    dsimp [j]
    omega
  have hnd : ¬p ∣ r + i + 1 := by
    rintro ⟨k, hk⟩
    have hk2 : k < 2 := by
      apply (Nat.mul_lt_mul_left hp.pos).mp
      rw [← hk]
      omega
    have hk0 : k ≠ 0 := by
      intro hk0
      simp [hk0] at hk
    have hk1 : k = 1 := by omega
    apply hne
    simpa [hk1] using hk
  simp only [F, one_div, padicValRat.inv, padicValRat.pow,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd,
    Nat.cast_zero, mul_zero, neg_zero, le_refl]

end ManuscriptChain.Beukers

#print axioms ManuscriptChain.Beukers.harmonic_below_prime_valuation_nonneg
#print axioms ManuscriptChain.Beukers.harmonic_outer_valuation_lower
#print axioms ManuscriptChain.Beukers.theorem_6_1_harmonic_bound
#print axioms ManuscriptChain.Beukers.theorem_6_1_part_two
#print axioms ManuscriptChain.Beukers.harmonic_outer_regular_valuation_nonneg
