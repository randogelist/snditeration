import Zetahyperbolic

/-!
Experimental scalar analytic inputs for the original Theorem 3.9.
The inputs are a Hurwitz pole-integral remainder and finite-character series
summation. They are not the positive-Gram, degree or real-root conclusions.
SOURCE_ONLY_UNCOMPILED; custom-axiom dependent.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Experimental.P03_09

def hurwitzSeries (k : ℕ) (θ : ℚ) : ℝ :=
  ∑' n : ℕ, 1 / ((n : ℝ) + (θ : ℝ)) ^ (2 * k + 1)

def shiftedPartialSum (k : ℕ) (θ : ℚ) (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range j, 1 / ((n : ℝ) + (θ : ℝ)) ^ (2 * k + 1)

/-- The actual positive-half-line integral, not an arbitrary functional model.
Its rational remainder is upstream data for defining the shifted rational
moment functional. Identification with Mathlib Hurwitz zeta is still separate. -/
axiom hurwitz_pole_integral_rational_remainder
    (k : ℕ) (hk : 0 < k) (θ : ℚ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (j : ℕ) :
    IntegrableOn
      (fun y : ℝ => ManuscriptChain.Hyperbolic.density k y /
        (y ^ 2 + ((j : ℝ) + (θ : ℝ)) ^ 2)) (Ioi (0 : ℝ)) ∧
      ∃ r : ℚ,
        (∫ y : ℝ in Ioi 0, ManuscriptChain.Hyperbolic.density k y /
          (y ^ 2 + ((j : ℝ) + (θ : ℝ)) ^ 2)) =
          ((j : ℝ) + (θ : ℝ)) ^ (2 * k) *
            (hurwitzSeries k θ - shiftedPartialSum k θ j) + (r : ℝ)

/-- The five primitive real character tables occurring at conductors 3,4,5,8.
These are explicit coefficient functions; a Mathlib character classification
and identification theorem is not assumed or supplied. -/
inductive CharacterTable where
  | minusThree | minusFour | five | eight | minusEight
  deriving DecidableEq

def conductor : CharacterTable → ℕ
  | .minusThree => 3
  | .minusFour => 4
  | .five => 5
  | .eight => 8
  | .minusEight => 8

def coefficient (c : CharacterTable) (n : ℕ) : ℝ :=
  match c with
  | .minusThree => if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0
  | .minusFour => if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0
  | .five => if n % 5 = 1 ∨ n % 5 = 4 then 1
      else if n % 5 = 2 ∨ n % 5 = 3 then -1 else 0
  | .eight => if n % 8 = 1 ∨ n % 8 = 7 then 1
      else if n % 8 = 3 ∨ n % 8 = 5 then -1 else 0
  | .minusEight => if n % 8 = 1 ∨ n % 8 = 3 then 1
      else if n % 8 = 5 ∨ n % 8 = 7 then -1 else 0

def numerator (c : CharacterTable) (z : ℝ) : ℝ :=
  match c with
  | .minusThree => z * (1 - z)
  | .minusFour => z * (1 - z ^ 2)
  | .five => z * (1 - z) ^ 2 * (1 + z)
  | .eight => z * (1 - z ^ 2) * (1 - z ^ 4)
  | .minusEight => z * (1 + z ^ 2) * (1 - z ^ 4)

def characterKernel (c : CharacterTable) (y : ℝ) : ℝ :=
  ∑' n : ℕ, coefficient c (n + 1) *
    Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y / (conductor c : ℝ)))

/-- An exact convergent power-series block identity. Positivity, exponential
kernel identification, all moment integrability and the pencil are still work. -/
axiom character_power_series_blocks (c : CharacterTable) (z : ℝ)
    (hz : 0 < z) (hz₁ : z < 1) :
    HasSum (fun n : ℕ => coefficient c (n + 1) * z ^ (n + 1))
      (numerator c z / (1 - z ^ conductor c))

end Experimental.P03_09
