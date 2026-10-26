import Zetahyperbolic

/-!
Experimental prerequisite interface. SOURCE_ONLY_UNCOMPILED.
The named axioms below are explicit research dependencies, not accepted
proofs. This module must stay outside the verified umbrella and axiom audit.
It does not assert the target theorem or upgrade its tier.
-/
noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace Experimental.P06_07

/-- Actual coupled signed density on the same unit square as Theorem 5.1. -/
def coupledDensity (k : ℕ) (a : ℕ → ℤ) (z : ℝ × ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k,
    (a m : ℝ) * (-Real.log (z.1 * z.2)) ^ (2 * m - 1) /
      (((2 * m).factorial : ℝ) * (1 - z.1 * z.2))

def modeDensity (k : ℕ) (a : ℕ → ℤ) (n : ℕ) (z : ℝ × ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k,
    (a m : ℝ) * (z.1 * z.2) ^ n * (-Real.log (z.1 * z.2)) ^ (2 * m - 1) /
      ((2 * m).factorial : ℝ)

/-- Explicit normalized Z-pencil: the slope is CC^T, not sum(a_m) CC^T. -/
def coupledEntry {h K : ℕ} (k : ℕ) (a : ℕ → ℤ)
    (c : Fin h → Fin (K + 1) → ℚ) (i j : Fin h) : ℚ[X] :=
  C (∑ r, ∑ t, c i r * c j t *
    ∑ m ∈ Finset.Icc 1 k,
      (a m : ℚ) * ManuscriptChain.Real.dualConstant (2 * m + 1) r.val t.val) +
  C (∑ r, c i r * c j r) * X

/-- Analytic bounded-kernel prerequisite, not the full Krein decomposition. -/
axiom coupled_kernel_square_integrable (k : ℕ) (a : ℕ → ℤ) :
  Integrable (fun z => coupledDensity k a z ^ 2)
    ManuscriptChain.Beukers.squareMeasure

/-- Absolute-integral summability before exchanging mode sums and L2 integrals. -/
axiom modes_absolute_integral_summable (k : ℕ) (a : ℕ → ℤ)
    (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo 0 1))) :
  Summable (fun n => ∫ z, ‖f z.1 * g z.2 * modeDensity k a n z‖
    ∂ManuscriptChain.Beukers.squareMeasure)

-- No axiom supplies positive/negative subspaces or the final q-adic valuation.
end Experimental.P06_07
