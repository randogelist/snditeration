import Zetahyperbolic.Section3.ActualReciprocalHankel

/-!
# The actual finite Stieltjes measure of reciprocal-root moments

The measure is the finite sum of Dirac masses at the inverse-square gaps.
Repeated roots and equal squared gaps retain their multiplicities. Every
moment is integrable and equals the actual even reciprocal-root power sum.
At a non-root shift the measure is concentrated on the strictly positive
half-line. No infinite-support or all-order strict-Hankel claim is made.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set

namespace LeanPaper.ReciprocalRootMoments

def reciprocalMeasure {h : ℕ} (r : Fin h → ℝ) (q : ℝ) : Measure ℝ :=
  ∑ i : Fin h, Measure.dirac (reciprocalAtom r q i)

theorem reciprocalMeasure_univ {h : ℕ} (r : Fin h → ℝ) (q : ℝ) :
    reciprocalMeasure r q univ = (h : ℝ≥0∞) := by
  simp [reciprocalMeasure, Measure.finsetSum_apply]

instance reciprocalMeasure_isFiniteMeasure {h : ℕ} (r : Fin h → ℝ) (q : ℝ) :
    IsFiniteMeasure (reciprocalMeasure r q) where
  measure_univ_lt_top := by rw [reciprocalMeasure_univ]; simp

theorem reciprocalMeasure_Iic_zero {h : ℕ} (r : Fin h → ℝ) (q : ℝ)
    (hr : ∀ i, r i ≠ q) : reciprocalMeasure r q (Iic 0) = 0 := by
  rw [reciprocalMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Measure.dirac_apply]
  exact Set.indicator_of_notMem (not_le.mpr (reciprocalAtom_pos r q hr i))
    (1 : ℝ → ℝ≥0∞)

theorem integrable_reciprocalMeasure {h : ℕ} (r : Fin h → ℝ) (q : ℝ)
    (f : ℝ → ℝ) : Integrable f (reciprocalMeasure r q) := by
  unfold reciprocalMeasure
  exact integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac (by simp))

theorem integral_reciprocalMeasure {h : ℕ} (r : Fin h → ℝ) (q : ℝ)
    (f : ℝ → ℝ) :
    (∫ x, f x ∂reciprocalMeasure r q) = ∑ i, f (reciprocalAtom r q i) := by
  unfold reciprocalMeasure
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp

theorem reciprocalEvenMoment_integral {h : ℕ} (r : Fin h → ℝ) (q : ℝ) (m : ℕ) :
    (∫ x, x ^ m ∂reciprocalMeasure r q) = reciprocalEvenMoment r q m :=
  integral_reciprocalMeasure r q (fun x => x ^ m)

/-- The manuscript's actual roots supply a finite positive-half-line measure
with all the stated even power sums as its moments. -/
theorem manuscript_stieltjes_measure
    (p : ManuscriptChain.Real.Parameters) (hp : ManuscriptChain.Real.Admissible p)
    (q : ℚ) (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Iic 0) = 0 ∧
      μ univ = (p.h : ℝ≥0∞) ∧ 0 < μ univ ∧
      ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) μ ∧
        (∫ x, x ^ m ∂μ) = reciprocalEvenMoment (manuscriptRoots p hp) (q : ℝ) m := by
  have hr : ∀ i, manuscriptRoots p hp i ≠ (q : ℝ) := by
    intro i heq
    apply hq
    simpa only [heq] using manuscriptRoots_eval p hp i
  refine ⟨reciprocalMeasure (manuscriptRoots p hp) (q : ℝ), inferInstance,
    reciprocalMeasure_Iic_zero _ _ hr, reciprocalMeasure_univ _ _, ?_, ?_⟩
  · rw [reciprocalMeasure_univ]
    exact_mod_cast Nat.sub_pos_of_lt hp.N_lt_K
  · intro m
    exact ⟨integrable_reciprocalMeasure _ _ _, reciprocalEvenMoment_integral _ _ m⟩

end LeanPaper.ReciprocalRootMoments

#print axioms LeanPaper.ReciprocalRootMoments.manuscript_stieltjes_measure
