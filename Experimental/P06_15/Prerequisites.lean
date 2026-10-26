import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_15

def betaTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ) ^ s)

/-- At s=1 use the actual integral, not an unordered `tsum` of a
conditionally convergent alternating series. Its ordered-series identification
remains a separate obligation; no pi/4 value is built into this definition.
For s≥2 the alternating series is absolutely convergent. -/
def betaValue (s : ℕ) : ℝ :=
  if s = 1 then ∫ u : ℝ in Ioo (0 : ℝ) 1, 1 / (1 + u ^ 2)
  else ∑' n : ℕ, betaTerm s n

def betaHarmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) ^ s)

def oddBetaDensity (k : ℕ) (u : ℝ) : ℝ :=
  (-Real.log u) ^ (2 * k) / ((Nat.factorial (2 * k) : ℝ) * (1 + u ^ 2))

def etaOne : ℝ := Real.log 2

/-- Independent transcendence input, explicit as nonvanishing of rational polynomials. -/
axiom upstream_pi_polynomial_nonvanishing (P : ℚ[X]) (hP : P ≠ 0) :
  (P.map (Rat.castHom ℝ)).eval Real.pi ≠ 0

/-- Elementary geometric kernel identity, before integrating its moments. -/
axiom upstream_unit_geometric (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
  HasSum (fun n : ℕ => (-1 : ℝ) ^ n * u ^ (2 * n)) (1 / (1 + u ^ 2))

export ManuscriptChain.UnitLogMoments (integral_pow_log integrable_pow_log)

end Experimental.P06_15
