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

namespace Experimental.P06_08

/-- Actual linear form, with the same zeta normalization as the verified project. -/
def linearForm (a b : ℤ) : ℝ :=
  (b : ℝ) * ManuscriptChain.Real.zeta 5 + (a : ℝ) * ManuscriptChain.Real.zeta 3

/-- External Apéry theorem: this branch must supply a verified import or discharge it. -/
axiom upstream_apery_irrational : Irrational (ManuscriptChain.Real.zeta 3)

/-- Upstream Theorem 4.5 qualitative assertion, not the present three-term conclusion. -/
axiom upstream_4_5_irrational (a b : ℤ)
    (hb : 0 < b) (hcone : (a : ℝ) < Real.pi ^ 2 / 3 * (b : ℝ)) :
    Irrational (linearForm a b)

/-- Upstream 4.5 ordinary threshold assertion. Computable effectivity is NOT encoded. -/
axiom upstream_4_5_measure (a b : ℤ)
    (hb : 0 < b) (hcone : (a : ℝ) < Real.pi ^ 2 / 3 * (b : ℝ)) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ q : ℕ, q₀ ≤ q → ∀ p : ℤ,
      1 / (q : ℝ) ^ 25687 < |linearForm a b - (p : ℝ) / (q : ℝ)|

end Experimental.P06_08
