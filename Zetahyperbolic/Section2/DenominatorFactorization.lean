import Zetahyperbolic.Section2.Moments
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
The canceled rational kernel in Definition 2.1 equals the original
manuscript weight D_N(t)^(2m) / D_K(t). These are polynomial identities,
so the later integral bridge refers to the actual paper denominator.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Real

theorem D_eq_prod_Icc (n : ℕ) :
    D n = ∏ a ∈ Finset.Icc 1 n, (X + C ((a : ℚ) ^ 2)) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
      rw [show D (n + 1) = D n * (X + C (((n + 1 : ℕ) : ℚ) ^ 2)) by
        simp only [D, Finset.prod_range_succ]]
      rw [Finset.prod_Icc_succ_top (by omega), ih]

theorem D_factorization (p : Parameters) (hNK : p.N ≤ p.K) :
    D p.K = D p.N * tailD p := by
  rw [D_eq_prod_Icc, D_eq_prod_Icc]
  unfold tailD
  simp only [← Finset.Ico_add_one_right_eq_Icc]
  exact (Finset.prod_Ico_consecutive
    (fun a : ℕ => (X + C ((a : ℚ) ^ 2) : ℚ[X]))
    (by omega : 1 ≤ p.N + 1) (by omega : p.N + 1 ≤ p.K + 1)).symm

end ManuscriptChain.Real
