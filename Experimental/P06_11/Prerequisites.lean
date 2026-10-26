import Zetahyperbolic

/-!
Experimental prerequisite interface only. SOURCE_ONLY_UNCOMPILED.
No target theorem is asserted here. Named axioms are local, explicit upstream
obligations on the concrete definitions below, not evidence of certification.
-/
noncomputable section
open scoped BigOperators Topology
open Polynomial Matrix MeasureTheory Set Filter

namespace Experimental.P06_11

def betaTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / (((2 * n + 1 : ℕ) : ℝ) ^ s)

def betaValue (s : ℕ) : ℝ := ∑' n : ℕ, betaTerm s n

def betaHarmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) ^ s)

def oddDenominator (n : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range n, (X + C (((2 * j + 1 : ℕ) : ℚ) ^ 2))

def quotientNumerator (N m i j : ℕ) : ℚ[X] :=
  oddDenominator N ^ (2 * m) * (X + 1) ^ (i + j)

def polynomialQuotient (K N m i j : ℕ) : ℚ[X] :=
  quotientNumerator N m i j / oddDenominator K

/-- Ordinary Bernoulli and Euler polynomials, explicit finite rational formulas. -/
def bernoulliPolynomial (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1),
    C ((n.choose j : ℚ) * bernoulli (n - j)) * X ^ j

def eulerPolynomial (n : ℕ) : ℚ[X] :=
  C (2 / ((n + 1 : ℕ) : ℚ)) *
    (bernoulliPolynomial (n + 1) - C ((2 : ℚ) ^ (n + 1)) *
      (bernoulliPolynomial (n + 1)).comp (C (1 / 2 : ℚ) * X))

/-- Independent shift law used to establish, not assume, p-distribution. -/
axiom upstream_euler_shift (n : ℕ) (x : ℚ) :
  (eulerPolynomial n).eval (x + 1) + (eulerPolynomial n).eval x = 2 * x ^ n

structure OddPrimeInput where
  p : ℕ
  prime : p.Prime
  odd : Odd p

end Experimental.P06_11
