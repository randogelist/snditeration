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

namespace Experimental.P06_04

/-- Exact odd-square denominator polynomial. -/
def oddDenominator (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range N, (X + C (((2 * j + 1 : ℕ) : ℚ) ^ 2))

/-- The explicit analytic kernel appearing in the printed differential formulas. -/
def betaKernel (y : ℝ) : ℝ := 1 / (2 * Real.cosh (Real.pi * y / 2))

def pureBetaFourWeight (y : ℝ) : ℝ :=
  -(y ^ 4 / (6 * Real.pi ^ 2)) *
    iteratedDeriv 3 (fun t => Real.pi * betaKernel t) y

def coupledBetaWeight (y : ℝ) : ℝ :=
  y ^ 4 / 24 *
    (-(4 / Real.pi ^ 2) * iteratedDeriv 3 betaKernel y + deriv betaKernel y)

/-- Upstream integration-by-parts boundary control for the actual sech kernel. -/
axiom beta_kernel_boundary_decay (d j : ℕ) (hj : j ≤ 3) :
  Filter.Tendsto (fun y : ℝ => y ^ d * iteratedDeriv j betaKernel y)
    Filter.atTop (nhds 0)

/-- Upstream integrability; no printed β-functional calibration is assumed. -/
axiom beta_kernel_derivative_integrable (d j : ℕ) (hj : j ≤ 3) :
  IntegrableOn (fun y : ℝ => y ^ d * iteratedDeriv j betaKernel y) (Ioi 0)

end Experimental.P06_04
