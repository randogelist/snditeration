import Zetahyperbolic.Section2.RationalFunctionals

/-!
# Regularity away from the finitely supported poles

The reduced denominator divides the explicit product of supported linear
factors. In particular the integer-pole domain is regular at zero when its
zero residue vanishes, and the square-pole domain is always regular at zero.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.SimplePole

variable {ι : Type*} [DecidableEq ι]

theorem denominator_dvd (node : ι → ℚ) (q : ℚ[X]) (c : ι →₀ ℚ) :
    RatFunc.denom (realize node (q,c)) ∣ ∏ i ∈ c.support, (X-C (node i)) := by
  let D : ℚ[X] := ∏ i ∈ c.support, (X-C (node i))
  let N : ℚ[X] := q*D + ∑ i ∈ c.support,
    C (c i) * ∏ j ∈ c.support.erase i, (X-C (node j))
  have hD : D ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact X_sub_C_ne_zero (node i)
  have hrepr : realize node (q,c) = algebraMap ℚ[X] (RatFunc ℚ) N /
      algebraMap ℚ[X] (RatFunc ℚ) D := by
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero hD)).2
    exact realize_mul_denominator node q c
  rw [hrepr]
  exact RatFunc.denom_div_dvd N D

/-- There are no hidden poles outside the stated finite pole support. -/
theorem eval_denom_ne_zero (node : ι → ℚ) (q : ℚ[X]) (c : ι →₀ ℚ)
    (a : ℚ) (ha : ∀ i ∈ c.support, node i ≠ a) :
    (RatFunc.denom (realize node (q,c))).eval a ≠ 0 := by
  have hprod : (∏ i ∈ c.support, (X-C (node i))).eval a ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simpa only [eval_sub, eval_X, eval_C] using sub_ne_zero.mpr (Ne.symm (ha i hi))
  obtain ⟨u, hu⟩ := denominator_dvd node q c
  intro hz
  apply hprod
  rw [hu, eval_mul, hz, zero_mul]

end ManuscriptChain.SimplePole

namespace ManuscriptChain.Tau

theorem eval_denom_zero_ne_zero (q : ℚ[X]) (c : ℤ →₀ ℚ) (hc : c 0 = 0) :
    (RatFunc.denom (SimplePole.realize integerNode (q,c))).eval 0 ≠ 0 := by
  apply SimplePole.eval_denom_ne_zero
  intro r hr hzero
  have hr0 : r = 0 := by
    dsimp [integerNode] at hzero
    exact_mod_cast hzero
  subst r
  exact (Finsupp.mem_support_iff.mp hr) hc

end ManuscriptChain.Tau

namespace ManuscriptChain.Mu

/-- Every rational function in Definition 2.1 is regular at the origin. -/
theorem rationalDomain_regular_at_zero (f : RationalDomain) :
    (RatFunc.denom (f : RatFunc ℚ)).eval 0 ≠ 0 := by
  obtain ⟨⟨q,c⟩, hf⟩ := f.property
  rw [← hf]
  apply SimplePole.eval_denom_ne_zero
  intro j hj
  unfold squareNode
  have hjpos : (0 : ℚ) < (j+1 : ℕ) := by positivity
  exact neg_ne_zero.mpr (pow_ne_zero _ (ne_of_gt hjpos))

end ManuscriptChain.Mu
