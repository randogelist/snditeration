import Zetahyperbolic

/-! SOURCE_ONLY_UNCOMPILED experimental prerequisite interface.
The literal printed normalization is not assumed. These are typed aliases of
already proved upstream facts for the explicitly corrected density. -/
noncomputable section
namespace Experimental.P03_02
open ManuscriptChain

theorem correctedGramInput (p : Real.Parameters) (s : ℝ) (hs : 0 < s) :
    (ContinuousWeight.gram p s).PosDef :=
  ContinuousWeight.gram_posDef p hs

theorem correctedSlopeInput (p : Real.Parameters) (s : ℝ) :
    (ContinuousWeight.direction p s).det ≠ 0 :=
  ContinuousWeight.direction_det_ne_zero p s

end Experimental.P03_02
