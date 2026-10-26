import Zetahyperbolic.Section2.RationalDifference

/-!
# Manuscript Theorem 5.4 — exact cancellation of even pole pairs

The theorem is stated directly for the existing actual integer-pole
rational-function domain and the already constructed rational tau functional.

For every positive integer j, including j = 1, the functional applied to
  (X - j)⁻¹ - (X + j)⁻¹
is the constant polynomial C(j⁻(2k+1)). The proof reduces to the
already verified harmonic finite-difference and reflection identities.
No new analytic or arithmetic assumption is introduced.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Tau

/-- The actual paper rational function (x-j)⁻¹ - (x+j)⁻¹. -/
def evenPolePair (j : ℕ) : RationalDomain :=
  SimplePole.ofData integerNode (0, Finsupp.single (j : ℤ) 1) -
    SimplePole.ofData integerNode (0, Finsupp.single (-(j : ℤ)) 1)

theorem evenPolePair_coe (j : ℕ) :
    (evenPolePair j : RatFunc ℚ) =
      (RatFunc.X - RatFunc.C (j : ℚ))⁻¹ -
        (RatFunc.X + RatFunc.C (j : ℚ))⁻¹ := by
  simp only [evenPolePair, Submodule.coe_sub]
  rw [rationalDomain_pole_coe (j : ℤ),
    rationalDomain_pole_coe (-(j : ℤ))]
  simp only [Int.cast_neg, map_neg, sub_neg_eq_add]
  simp

/-- Actual integer-pole τ, with no exceptional omission at j=1. -/
theorem evenPolePair_cancellation (k j : ℕ) (hj : 1 ≤ j) :
    rationalFunctional k (evenPolePair j) =
      C (((j : ℚ) ^ (2 * k + 1))⁻¹) := by
  have hj0 : (j : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < j))
  have hreflect :
      tauPolePoly k (-(j : ℤ)) = tauPolePoly k ((j : ℤ) - 1) := by
    have h := tauPolePoly_reflect k ((j : ℤ) - 1)
    simpa only [show (-1 - ((j : ℤ) - 1) : ℤ) = -(j : ℤ) by omega] using h
  unfold evenPolePair
  rw [map_sub, rationalFunctional_pole, rationalFunctional_pole]
  change tauPolePoly k (j : ℤ) - tauPolePoly k (-(j : ℤ)) = _
  rw [hreflect]
  calc
    tauPolePoly k (j : ℤ) - tauPolePoly k ((j : ℤ) - 1) =
        -(tauPolePoly k ((j : ℤ) - 1) - tauPolePoly k (j : ℤ)) := by abel
    _ = -(C (-(((j : ℚ) ^ (2 * k + 1))⁻¹))) := by
      rw [tau_difference_pole k (j : ℤ) hj0]
      simp
    _ = C (((j : ℚ) ^ (2 * k + 1))⁻¹) := by simp

/-- The j=1 endpoint, where the printed proof's intermediate division step fails. -/
theorem evenPolePair_one (k : ℕ) :
    rationalFunctional k (evenPolePair 1) = C (1 : ℚ) := by
  simpa using evenPolePair_cancellation k 1 (by omega)

/-- Finite rational linearity extends the exact cancellation to any
finitely supported sum of positive-index even pole pairs. -/
theorem finite_evenPolePair_cancellation
    (k : ℕ) (s : Finset ℕ) (c : ℕ → ℚ)
    (hs : ∀ j ∈ s, 1 ≤ j) :
    rationalFunctional k (∑ j ∈ s, c j • evenPolePair j) =
      C (∑ j ∈ s, c j * (((j : ℚ) ^ (2 * k + 1))⁻¹)) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, evenPolePair_cancellation k j (hs j hj)]
  simp [Polynomial.smul_C, smul_eq_mul]

end ManuscriptChain.Tau
