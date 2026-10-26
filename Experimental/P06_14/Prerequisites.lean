import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_14

def betaTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ) ^ s)

def betaValue (s : ℕ) : ℝ := ∑' n : ℕ, betaTerm s n

def betaHarmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) ^ s)

def secantKernel (z : ℝ) : ℝ := 1 / (2 * Real.cosh z)

def secantMode (n : ℕ) (z : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * z))

def iteratedDerivative : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (iteratedDerivative n f)

/-- Real rescaling operation; its Jacobian has not been identified with a rational functional. -/
def scaleWeight (w : ℝ → ℝ) (v : ℝ) : ℝ := -4 * w (2 * v)

/-- Independent Fourier/sech identity used to reconstruct the analytic beta functional. -/
axiom upstream_sech_cosine_transform (a : ℝ) :
  (∫ x : ℝ in Ioi 0, Real.cos (a * x) / Real.cosh x) =
    Real.pi / (2 * Real.cosh (Real.pi * a / 2))

export ManuscriptChain.UnitLogMoments (integral_pow_log integrable_pow_log)
export ManuscriptChain.Hyperbolic (density density_pos)

end Experimental.P06_14
