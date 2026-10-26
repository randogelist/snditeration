import Zetahyperbolic.Section4.Transfer

/-! The local radius used in the root-geometric proof of Theorem 4.1. -/
noncomputable section
namespace ManuscriptChain.Spectral

def comparisonRadius (n : ℕ) (bound : ℝ) : ℝ :=
  1 / (8 * ((n : ℝ) + 1) * bound)

theorem comparisonRadius_pos (n : ℕ) (bound : ℝ) (hbound : 0 < bound) :
    0 < comparisonRadius n bound := by
  unfold comparisonRadius
  positivity

end ManuscriptChain.Spectral
