import Zetahyperbolic

/-!
EXPERIMENTAL PREREQUISITE LAYER — SOURCE_ONLY_UNCOMPILED.
The axioms in this file are explicit research assumptions. They are not proofs,
not part of the certified umbrella, and may not enter a production proof receipt.
No full target theorem or contradiction is admitted here.
-/
noncomputable section
open scoped BigOperators
open Polynomial MeasureTheory Set

namespace Experimental.P04_06

/-- Classical arcsine density used in the printed Jensen comparison. -/
def arcsineDensity (L t : ℝ) : ℝ :=
  1 / (Real.pi * Real.sqrt (t * (L - t)))

/-- Explicit logarithmic expression for 2 arsinh(u/sqrt L)+log(L/4). -/
def arcsinePotentialValue (L u : ℝ) : ℝ :=
  2 * Real.log (u / Real.sqrt L + Real.sqrt (1 + (u / Real.sqrt L)^2)) +
    Real.log (L / 4)

axiom arcsine_probability_input (L : ℝ) (hL : 0 < L) :
    IntegrableOn (arcsineDensity L) (Set.Ioo 0 L) ∧
      (∫ t in Set.Ioo 0 L, arcsineDensity L t) = 1

axiom arcsine_log_potential_input (L u : ℝ) (hL : 0 < L) (hu : 0 < u) :
    IntegrableOn (fun t => Real.log (t + u^2) * arcsineDensity L t)
      (Set.Ioo 0 L) ∧
    (∫ t in Set.Ioo 0 L, Real.log (t + u^2) * arcsineDensity L t) =
      arcsinePotentialValue L u

end Experimental.P04_06
