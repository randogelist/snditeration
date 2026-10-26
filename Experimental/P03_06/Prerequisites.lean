import Zetahyperbolic

/-! SOURCE_ONLY_UNCOMPILED. Actual finite-node Gram expansion is an
upstream algebraic input to a corrected finite-support moment statement.
Strict positivity in all orders is neither assumed nor asserted. -/
noncomputable section
open scoped BigOperators
namespace Experimental.P03_06
open ManuscriptChain

def actualRoot (p : Real.Parameters) (i : Fin p.h) : ℝ :=
  Real.zeta p.weight -
    (Spectral.actualEigenvalues (Real.manuscriptPencil p) i)⁻¹

def reciprocalSquareNode (p : Real.Parameters) (q : ℚ) (i : Fin p.h) : ℝ :=
  ((actualRoot p i - (q : ℝ))⁻¹) ^ 2

def finiteEvenMoment (p : Real.Parameters) (q : ℚ) (r : ℕ) : ℝ :=
  ∑ i, reciprocalSquareNode p q i ^ r

/-- Finite polynomial expansion on the actual spectral nodes. This algebraic
identity alone supplies no rank, rationality, logarithmic derivative or limit. -/
axiom actualFiniteMomentGramExpansion (p : Real.Parameters) (q : ℚ)
    (r : ℕ) (c : Fin r → ℝ) :
  (∑ i : Fin r, ∑ j : Fin r,
    c i * c j * finiteEvenMoment p q (i.val + j.val)) =
  ∑ a : Fin p.h,
    (∑ i : Fin r, c i * reciprocalSquareNode p q a ^ i.val) ^ 2

end Experimental.P03_06
