import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_13

def secantKernel (z : ℝ) : ℝ := 1 / (2 * Real.cosh z)

def secantMode (n : ℕ) (z : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * z))

/-- Base geometric expansion, before applying any differential operator. -/
axiom upstream_secant_laplace_expansion (z : ℝ) (hz : 0 < z) :
  HasSum (fun n : ℕ => secantMode n z) (secantKernel z)

/-- Finite operator data; the sign is kept in its original factor order. -/
def centralOperator : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => fun z =>
      (((2 * n + 1 : ℕ) : ℝ) ^ 2) * centralOperator n f z -
        deriv (deriv (centralOperator n f)) z

def finalOperator (k : ℕ) (z : ℝ) : ℝ :=
  -deriv (centralOperator (k - 1) secantKernel) z

export ManuscriptChain.Hyperbolic (summable_exponentialTerm)

end Experimental.P06_13
