import Zetahyperbolic.Section5.BeukersPolynomialIntegral
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The fixed-degree obstruction for the actual rational Beukers form

Theorem 5.2(3) keeps the opening degree bound K while asking for positive and
negative rational h-dimensional polynomial subspaces. Such spaces must be
disjoint, so 2h ≤ K+1. The permitted instance K=h=2 therefore refutes the
fixed-K conclusion. This does not refute a revised sufficiently-large-K
statement, and does not settle the separate uncontrolled infinite-tail issue.

The generic disjointness argument follows the companion's
LeanPaper.KreinDimensionObstruction, source
86ca99a23d65cde4880a9005a49076c43e7bc968. Here the scalar field is ℚ, as in
the manuscript, and the endpoint uses the destination's actual Beukers
polynomial integral rather than an unspecified real-valued expression.
-/

noncomputable section
open MeasureTheory Module

namespace ManuscriptChain.Beukers

/-- Strict positive and negative rational subspaces have trivial intersection.
No bilinearity or spectral hypothesis is needed for this dimension obstruction. -/
theorem rational_positive_negative_disjoint
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (q : V → ℝ) (S T : Submodule ℚ V)
    (hS : ∀ v ∈ S, v ≠ 0 → 0 < q v)
    (hT : ∀ v ∈ T, v ≠ 0 → q v < 0) : Disjoint S T := by
  rw [Submodule.disjoint_def]
  intro v hvS hvT
  by_contra hn
  exact lt_asymm (hS v hvS hn) (hT v hvT hn)

/-- Necessary fixed-degree dimension bound for the actual Beukers moments. -/
theorem actual_positive_negative_dimension_bound (K h : ℕ)
    (S T : Submodule ℚ (Fin (K + 1) → ℚ))
    (hS : ∀ c ∈ S, c ≠ 0 → 0 < polynomialMomentForm c c)
    (hT : ∀ c ∈ T, c ≠ 0 → polynomialMomentForm c c < 0)
    (dS : finrank ℚ S = h) (dT : finrank ℚ T = h) :
    2 * h ≤ K + 1 := by
  have hd := Submodule.finrank_add_finrank_le_of_disjoint
    (rational_positive_negative_disjoint
      (fun c : Fin (K + 1) → ℚ => polynomialMomentForm c c) S T hS hT)
  simp only [dS, dT, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hd
  omega

/-- The same necessary inequality stated with the literal product integral. -/
theorem actual_integral_cones_require_twice_dimension (K h : ℕ)
    (S T : Submodule ℚ (Fin (K + 1) → ℚ))
    (hS : ∀ c ∈ S, c ≠ 0 →
      0 < ∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue c z.2 *
        density z ∂squareMeasure)
    (hT : ∀ c ∈ T, c ≠ 0 →
      (∫ z, coefficientPolynomialValue c z.1 * coefficientPolynomialValue c z.2 *
        density z ∂squareMeasure) < 0)
    (dS : finrank ℚ S = h) (dT : finrank ℚ T = h) :
    2 * h ≤ K + 1 := by
  simp_rw [integral_polynomial_product_eq_momentForm] at hS hT
  exact actual_positive_negative_dimension_bound K h S T hS hT dS dT

/-- K=h=2 is permitted by the theorem's opening K≥h≥1 assumptions,
but its fixed-degree positive/negative subspace conclusion is impossible. -/
theorem actual_fixed_K_two_h_two_impossible :
    ¬ ∃ S T : Submodule ℚ (Fin 3 → ℚ),
      finrank ℚ S = 2 ∧ finrank ℚ T = 2 ∧
      (∀ c ∈ S, c ≠ 0 → 0 < polynomialMomentForm c c) ∧
      (∀ c ∈ T, c ≠ 0 → polynomialMomentForm c c < 0) := by
  rintro ⟨S, T, dS, dT, hS, hT⟩
  have hd := actual_positive_negative_dimension_bound 2 2 S T hS hT dS dT
  omega

end ManuscriptChain.Beukers
