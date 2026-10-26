import Zetahyperbolic.Section5.ActualKreinDimensionObstruction
import Zetahyperbolic.Section5.BetaBeukersMoments

/-!
# Fixed-degree cone obstruction in Theorems 6.7 and 6.17

Both printed conclusions retain the opening degree bound K and ask for two
rational h-dimensional spaces, one strictly positive and the other strictly
negative. Their intersection must vanish. Thus 2h <= K+1 is necessary,
independently of the number and signs of the weights. In particular the
permitted instance K=h=2 is impossible.

The endpoint below uses the literal combined harmonic pencil in 6.17;
setting the beta tuple to zero gives exactly the pencil in 6.7. The center
is the actual finite combination of the zeta and beta Dirichlet series.
This refutes the fixed-K cone quantifiers, not the independent hyperbolicity
or local determinant assertions. Allowing sufficiently large K depending
on h is a necessary repair; it does not supply infinite-tail estimates.
-/

noncomputable section
open scoped BigOperators
open Module

namespace ManuscriptChain.Chapter6ConeDimension

/-- The common actual center in 6.17, using the original convergent series. -/
def center {k : ℕ} (b a : Fin k → ℤ) : ℝ :=
  ∑ m : Fin k,
    ((b m : ℝ) * Real.zeta (2 * (m.val + 1) + 1) +
      (a m : ℝ) * BetaBeukers.betaValue (2 * (m.val + 1)))

/-- The constant monomial entry of the printed combined pencil. -/
def constantEntry {k : ℕ} (b a : Fin k → ℤ) (r s : ℕ) : ℚ :=
  if r = s then
    -∑ m : Fin k,
      ((b m : ℚ) * Real.harmonic (2 * (m.val + 1) + 1) r +
        (a m : ℚ) * BetaBeukers.betaHarmonic (2 * (m.val + 1)) (2 * r))
  else
    (∑ m : Fin k,
      ((b m : ℚ) / (2 * (m.val + 1)) *
          (Real.harmonic (2 * (m.val + 1)) r -
            Real.harmonic (2 * (m.val + 1)) s) +
        (a m : ℚ) / (4 * (2 * (m.val + 1) - 1)) *
          (BetaBeukers.betaHarmonic (2 * (m.val + 1) - 1) (2 * r) -
            BetaBeukers.betaHarmonic (2 * (m.val + 1) - 1) (2 * s)))) /
      ((r : ℚ) - s)

/-- Literal monomial pencil, evaluated at the actual zeta--beta center. -/
def entry {k : ℕ} (b a : Fin k → ℤ) (r s : ℕ) : ℝ :=
  (constantEntry b a r s : ℝ) + if r = s then center b a else 0

/-- The printed quadratic pencil on rational polynomial coefficients.
For 6.17 the vector represents a polynomial in x^4; its dimension is still K+1. -/
def quadratic {k K : ℕ} (b a : Fin k → ℤ) (c : Fin (K + 1) → ℚ) : ℝ :=
  ∑ r : Fin (K + 1), ∑ s : Fin (K + 1),
    (c r : ℝ) * (c s : ℝ) * entry b a r.val s.val

/-- The dimension obstruction applies to any quadratic form whatsoever. -/
theorem fixed_degree_dimension_bound (K h : ℕ)
    (q : (Fin (K + 1) → ℚ) → ℝ)
    (S T : Submodule ℚ (Fin (K + 1) → ℚ))
    (hS : ∀ c ∈ S, c ≠ 0 → 0 < q c)
    (hT : ∀ c ∈ T, c ≠ 0 → q c < 0)
    (dS : finrank ℚ S = h) (dT : finrank ℚ T = h) :
    2 * h ≤ K + 1 := by
  have hd := Submodule.finrank_add_finrank_le_of_disjoint
    (Beukers.rational_positive_negative_disjoint q S T hS hT)
  simp only [dS, dT, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hd
  omega

/-- The literal combined harmonic pencil must obey the necessary dimension bound. -/
theorem combined_cones_require_twice_dimension {k : ℕ} (K h : ℕ)
    (b a : Fin k → ℤ) (S T : Submodule ℚ (Fin (K + 1) → ℚ))
    (hS : ∀ c ∈ S, c ≠ 0 → 0 < quadratic b a c)
    (hT : ∀ c ∈ T, c ≠ 0 → quadratic b a c < 0)
    (dS : finrank ℚ S = h) (dT : finrank ℚ T = h) :
    2 * h ≤ K + 1 :=
  fixed_degree_dimension_bound K h (quadratic b a) S T hS hT dS dT

/-- Refutation of the fixed-K conclusion in 6.17(2), for every tuple. -/
theorem theorem_6_17_fixed_degree_two_impossible {k : ℕ} (b a : Fin k → ℤ) :
    ¬ ∃ S T : Submodule ℚ (Fin 3 → ℚ),
      finrank ℚ S = 2 ∧ finrank ℚ T = 2 ∧
      (∀ c ∈ S, c ≠ 0 → 0 < quadratic b a c) ∧
      (∀ c ∈ T, c ≠ 0 → quadratic b a c < 0) := by
  rintro ⟨S, T, dS, dT, hS, hT⟩
  have hd := combined_cones_require_twice_dimension 2 2 b a S T hS hT dS dT
  omega

/-- Refutation of the fixed-K conclusion in 6.7(2), the pure-zeta specialization. -/
theorem theorem_6_7_fixed_degree_two_impossible {k : ℕ} (b : Fin k → ℤ) :
    ¬ ∃ S T : Submodule ℚ (Fin 3 → ℚ),
      finrank ℚ S = 2 ∧ finrank ℚ T = 2 ∧
      (∀ c ∈ S, c ≠ 0 → 0 < quadratic b 0 c) ∧
      (∀ c ∈ T, c ≠ 0 → quadratic b 0 c < 0) :=
  theorem_6_17_fixed_degree_two_impossible b 0

end ManuscriptChain.Chapter6ConeDimension
