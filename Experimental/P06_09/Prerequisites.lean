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

namespace Experimental.P06_09

/-- Exact rational numerator and denominator of the printed triple-pole family. -/
def tripleNumerator (n : ℕ) : ℚ[X] :=
  C (((6 * n).factorial : ℚ) ^ 3) *
    ∏ j ∈ Finset.Icc 1 n, (X - C ((j : ℚ) - 1)) ^ 6

def tripleDenominator (n : ℕ) : ℚ[X] :=
  ∏ k ∈ Finset.range (6 * n + 1), (X + C (k : ℚ)) ^ 3

def tripleRational (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (tripleNumerator n) /
    algebraMap ℚ[X] (RatFunc ℚ) (tripleDenominator n)

/-- Upstream actual finite partial-fraction existence. No claimed residue formula. -/
axiom triple_partial_fraction (n : ℕ) (hn : 0 < n) (P : ℚ[X])
    (hP : P.natDegree < 6 * n) :
    ∃ c : Fin (6 * n + 1) → Fin 3 → ℚ,
      tripleRational n * algebraMap ℚ[X] (RatFunc ℚ) P =
        ∑ k, ∑ r,
          algebraMap ℚ (RatFunc ℚ) (c k r) /
            (algebraMap ℚ[X] (RatFunc ℚ) (X + C (k.val : ℚ))) ^ (r.val + 1)

/-- Generic finite Hermite interpolation at distinct actual rational nodes. -/
axiom rational_three_jet_interpolation (h : ℕ) (hh : 0 < h)
    (u a b c : Fin h → ℚ) (hu : Function.Injective u) :
    ∃ P : ℚ[X], P.natDegree < 3 * h ∧
      ∀ i, P.eval (u i) = a i ∧ P.derivative.eval (u i) = b i ∧
        P.derivative.derivative.eval (u i) = c i

/-- Actual finite harmonic residual used in the highest-weight arithmetic. -/
def harmonicResidual (s q r : ℕ) : ℚ :=
  ManuscriptChain.Real.harmonic s r -
    if q ≤ r then 1 / (q : ℚ) ^ s else 0

axiom upstream_harmonic_residual_p_integral (q s r : ℕ)
    (hq : Nat.Prime q) (hs : 0 < s) (hr : r < 2 * q) :
    ¬ q ∣ (harmonicResidual s q r).den

end Experimental.P06_09
