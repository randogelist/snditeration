import Zetahyperbolic.Section2.Moments
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual simple-pole rational-function domains

A polynomial and finitely supported residues determine a rational function.
The realization is injective when the pole nodes are distinct. Consequently,
linear functionals specified on polynomial and pole generators descend to
an actual subspace of `RatFunc ℚ`, with no representation-invariance premise.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.SimplePole

variable {ι : Type*} [DecidableEq ι]

abbrev Data (ι : Type*) := ℚ[X] × (ι →₀ ℚ)

def polynomialEmbedding : ℚ[X] →ₗ[ℚ] RatFunc ℚ :=
  (IsScalarTower.toAlgHom ℚ ℚ[X] (RatFunc ℚ)).toLinearMap

def realize (node : ι → ℚ) : Data ι →ₗ[ℚ] RatFunc ℚ :=
  polynomialEmbedding.comp (LinearMap.fst ℚ ℚ[X] (ι →₀ ℚ)) +
    (Finsupp.linearCombination ℚ (fun a =>
      (algebraMap ℚ[X] (RatFunc ℚ) (X - C (node a)))⁻¹)).comp
        (LinearMap.snd ℚ ℚ[X] (ι →₀ ℚ))

theorem realize_apply (node : ι → ℚ) (q : ℚ[X]) (c : ι →₀ ℚ) :
    realize node (q,c) = algebraMap ℚ[X] (RatFunc ℚ) q +
      ∑ a ∈ c.support, algebraMap ℚ[X] (RatFunc ℚ) (C (c a)) /
        algebraMap ℚ[X] (RatFunc ℚ) (X - C (node a)) := by
  simp only [realize, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Finsupp.linearCombination_apply,
    Finsupp.sum, polynomialEmbedding, AlgHom.toLinearMap_apply,
    IsScalarTower.coe_toAlgHom]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [Algebra.smul_def, div_eq_mul_inv]
  congr 1
  rw [IsScalarTower.algebraMap_eq ℚ ℚ[X] (RatFunc ℚ)]
  rfl

theorem realize_mul_denominator (node : ι → ℚ) (q : ℚ[X]) (c : ι →₀ ℚ) :
    realize node (q,c) *
        algebraMap ℚ[X] (RatFunc ℚ) (∏ a ∈ c.support, (X - C (node a))) =
      algebraMap ℚ[X] (RatFunc ℚ)
        (q * (∏ a ∈ c.support, (X - C (node a))) +
          ∑ a ∈ c.support, C (c a) *
            ∏ b ∈ c.support.erase a, (X - C (node b))) := by
  classical
  rw [realize_apply, add_mul, Finset.sum_mul, map_add, map_mul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [show (∏ b ∈ c.support, (X - C (node b))) =
      (X - C (node a)) * ∏ b ∈ c.support.erase a, (X - C (node b)) from
        (Finset.mul_prod_erase c.support _ ha).symm]
  rw [map_mul, map_mul]
  have hd : algebraMap ℚ[X] (RatFunc ℚ) (X - C (node a)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero (node a))
  field_simp

theorem realize_eq_zero (node : ι → ℚ) (hn : Function.Injective node)
    (q : ℚ[X]) (c : ι →₀ ℚ) (hz : realize node (q,c) = 0) :
    q = 0 ∧ c = 0 := by
  classical
  have hid := realize_mul_denominator node q c
  rw [hz, zero_mul] at hid
  have hpoly : q * (∏ a ∈ c.support, (X - C (node a))) +
      ∑ a ∈ c.support, C (c a) *
        ∏ b ∈ c.support.erase a, (X - C (node b)) = 0 :=
    (RatFunc.algebraMap_injective ℚ) (by simpa using hid.symm)
  have hc : c = 0 := by
    apply Finsupp.ext
    intro a
    by_cases ha : a ∈ c.support
    · have hev := congrArg (Polynomial.eval (node a)) hpoly
      have hprod : (∏ b ∈ c.support, (X - C (node b))).eval (node a) = 0 := by
        rw [eval_prod]
        apply Finset.prod_eq_zero ha
        simp
      rw [eval_add, eval_mul, hprod, mul_zero, zero_add, eval_finsetSum, eval_zero] at hev
      have hsum : (∑ b ∈ c.support,
          (C (c b) * ∏ d ∈ c.support.erase b, (X - C (node d))).eval (node a)) =
          c a * ∏ b ∈ c.support.erase a, (node a - node b) := by
        rw [Finset.sum_eq_single a]
        · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
        · intro b hb hba
          rw [eval_mul]
          have hp : (∏ d ∈ c.support.erase b, (X - C (node d))).eval (node a) = 0 := by
            rw [eval_prod]
            apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩)
            simp
          rw [hp, mul_zero]
        · intro hnot
          exact (hnot ha).elim
      rw [hsum] at hev
      have hne : (∏ b ∈ c.support.erase a, (node a - node b)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro b hb
        exact sub_ne_zero.mpr (fun hab => (Finset.mem_erase.mp hb).1 (hn hab).symm)
      simpa using (mul_eq_zero.mp hev).resolve_right hne
    · simpa using Finsupp.notMem_support_iff.mp ha
  refine ⟨?_, hc⟩
  subst c
  simpa [realize_apply] using (RatFunc.algebraMap_injective ℚ)
    (by simpa [realize_apply] using hz)

theorem realize_injective (node : ι → ℚ) (hn : Function.Injective node) :
    Function.Injective (realize node) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro d hd
  rcases d with ⟨q,c⟩
  rcases realize_eq_zero node hn q c hd with ⟨rfl,rfl⟩
  rfl

end ManuscriptChain.SimplePole
