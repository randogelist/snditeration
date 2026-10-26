import Zetahyperbolic

/-!
Experimental analytic prerequisites for Theorem 3.8.
The new axioms concern the actual Laplace density and local domination of its
moment derivatives. They do not assert a determinant derivative, a CD identity,
or spectral coincidence. SOURCE_ONLY_UNCOMPILED; custom-axiom dependent.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Experimental.P03_08

def laplaceTerm (k n : ℕ) (τ y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * k) *
    Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * τ * y))

def density (k : ℕ) (τ y : ℝ) : ℝ :=
  (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
    y ^ (2 * k + 1) * ∑' n : ℕ, laplaceTerm k n τ y

def densityDerivative (k : ℕ) (τ y : ℝ) : ℝ :=
  (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
    y ^ (2 * k + 1) *
      ∑' n : ℕ, (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y)) *
        laplaceTerm k n τ y

def rationalWeight (p : ManuscriptChain.Real.Parameters) (y : ℝ) : ℝ :=
  ManuscriptChain.Real.evalQ (ManuscriptChain.Real.D p.N) (y ^ 2) ^ (2 * p.m) /
    ManuscriptChain.Real.evalQ (ManuscriptChain.Real.D p.K) (y ^ 2)

def momentIntegrand (p : ManuscriptChain.Real.Parameters) (e : ℕ)
    (τ y : ℝ) : ℝ :=
  y ^ (2 * e) * rationalWeight p y * density p.k τ y

def momentDerivativeIntegrand (p : ManuscriptChain.Real.Parameters) (e : ℕ)
    (τ y : ℝ) : ℝ :=
  y ^ (2 * e) * rationalWeight p y * densityDerivative p.k τ y

/-- Pointwise parameter differentiation of the explicitly defined exponential
series. A future proof must justify differentiation of the infinite sum. -/
axiom laplace_density_hasDerivAt (k : ℕ) (τ y : ℝ)
    (hτ : 0 < τ) (hy : 0 < y) :
    HasDerivAt (fun u : ℝ => density k u y) (densityDerivative k τ y) τ

/-- One integrable majorant on a genuine positive parameter neighborhood,
for each actual rational moment and its proposed parameter derivative. -/
axiom laplace_moment_local_domination
    (p : ManuscriptChain.Real.Parameters) (hp : ManuscriptChain.Real.Admissible p)
    (e : ℕ) (τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ∃ ε : ℝ, 0 < ε ∧ ε < τ₀ ∧ ∃ g : ℝ → ℝ,
      IntegrableOn g (Ioi (0 : ℝ)) ∧
      ∀ τ : ℝ, |τ - τ₀| < ε → ∀ y : ℝ, 0 < y →
        ‖momentIntegrand p e τ y‖ ≤ g y ∧
        ‖momentDerivativeIntegrand p e τ y‖ ≤ g y

theorem base_gram_positive (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    (ManuscriptChain.Real.gram p (ManuscriptChain.Real.zeta p.weight)).PosDef :=
  ManuscriptChain.GRAM_POSITIVE p hp

end Experimental.P03_08
