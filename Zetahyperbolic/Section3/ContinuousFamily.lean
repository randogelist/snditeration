import Zetahyperbolic.Section3.ContinuousParameter

/-!
# Continuity of the actual real-parameter pencil

The integral Gram entries are continuous by endpoint-kernel domination.
This module completes the connection to the displayed family: its pole
weights and slope, its actual zeta center, and every matrix and determinant
evaluation vary continuously on the half-line s > 1.

The corrected density normalization and the original rational odd-weight
identification remain those in `ContinuousPencil`.
-/

noncomputable section
open Set Topology

namespace ManuscriptChain.ContinuousWeight

theorem continuous_poleWeight (p : Real.Parameters) (a : Fin p.h) :
    Continuous (fun s => poleWeight p s a) := by
  have ha : (PoleDiagonalization.poleIndex p a : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (PoleDiagonalization.poleIndex_pos p a)
  unfold poleWeight
  exact continuous_const.mul
    ((Real.continuous_const_rpow ha).comp (continuous_id.sub continuous_const))

theorem continuous_direction (p : Real.Parameters) : Continuous (direction p) := by
  unfold direction
  exact (continuous_const.mul
    ((continuous_pi fun a => continuous_poleWeight p a).matrix_diagonal)).mul continuous_const

theorem continuousAt_center {s : ℝ} (hs : 1 < s) : ContinuousAt center s := by
  have hs' : (s : ℂ) ≠ 1 := by exact_mod_cast hs.ne'
  have hz := (differentiableAt_riemannZeta hs').continuousAt
  exact Complex.continuous_re.continuousAt.comp
    (hz.comp Complex.continuous_ofReal.continuousAt)

theorem continuousAt_matrixAt (p : Real.Parameters) (x : ℝ) {s : ℝ} (hs : 1 < s) :
    ContinuousAt (fun t => (pencil p t).matrixAt x) s := by
  change ContinuousAt (fun t => gram p t + (x - center t) • direction p t) s
  exact (continuousAt_gram p (lt_trans zero_lt_one hs)).add
    ((continuousAt_const.sub (continuousAt_center hs)).smul
      (continuous_direction p).continuousAt)

theorem continuousOn_matrixAt (p : Real.Parameters) (x : ℝ) :
    ContinuousOn (fun s => (pencil p s).matrixAt x) (Ioi 1) :=
  fun _ hs => (continuousAt_matrixAt p x hs).continuousWithinAt

theorem continuousAt_detValue (p : Real.Parameters) (x : ℝ) {s : ℝ} (hs : 1 < s) :
    ContinuousAt (fun t => (pencil p t).detValue x) s :=
  continuous_id.matrix_det.continuousAt.comp (continuousAt_matrixAt p x hs)

theorem continuousAt_detPolynomial_eval
    (p : Real.Parameters) (x : ℝ) {s : ℝ} (hs : 1 < s) :
    ContinuousAt (fun t => (pencil p t).detPolynomial.eval x) s := by
  simpa only [Spectral.SymmetricAffinePencil.eval_detPolynomial] using
    continuousAt_detValue p x hs

theorem continuousOn_detPolynomial_eval (p : Real.Parameters) (x : ℝ) :
    ContinuousOn (fun s => (pencil p s).detPolynomial.eval x) (Ioi 1) :=
  fun _ hs => (continuousAt_detPolynomial_eval p x hs).continuousWithinAt

end ManuscriptChain.ContinuousWeight

#print axioms ManuscriptChain.ContinuousWeight.continuousAt_matrixAt
#print axioms ManuscriptChain.ContinuousWeight.continuousAt_detPolynomial_eval
