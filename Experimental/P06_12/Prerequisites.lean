import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_12

def betaFourWeight (u : ℝ) : ℝ :=
  (Real.pi / 24) * u ^ 3 * Real.sinh (Real.pi * u) /
    Real.cosh (Real.pi * u) ^ 4 * (Real.cosh (Real.pi * u) ^ 2 - 6)

def denominator (n : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.range n, (t + (((j + 1 : ℕ) : ℝ) ^ 2))

def gramEntry (K N m i j : ℕ) (r : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    denominator N (u ^ 2) ^ (2 * m) * u ^ (2 * (i + j)) /
      denominator K (u ^ 2) * (u ^ 2 - r ^ 2) * betaFourWeight u

/-- Reference root data; contains no positive-Gram or rational-approximation conclusion. -/
structure ReferenceRootInput where
  root : ℝ
  positive : 0 < root
  cosh_square : Real.cosh (Real.pi * root) ^ 2 = 6

/-- Upstream analytic domination needed before perturbing any rational parameter. -/
axiom upstream_beta_four_moments_integrable (e : ℕ) :
  IntegrableOn (fun u : ℝ => u ^ e * betaFourWeight u) (Ioi 0)

end Experimental.P06_12
