import Zetahyperbolic.Section3.HyperbolicDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
The nonzero atomless measure induced by the hyperbolic weight (3.1).
This does not assert any pole-integral identity.
-/

noncomputable section
open MeasureTheory Set

namespace ManuscriptChain.Hyperbolic

def baseMeasure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun y => ENNReal.ofReal (density k y))

instance baseMeasure_nullSingleton (k : ℕ) : NullSingletonClass (baseMeasure k) := by
  unfold baseMeasure
  infer_instance

theorem baseMeasure_nonzero (k : ℕ) : baseMeasure k ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ baseMeasure k := by
    apply withDensity_absolutelyContinuous'
      (measurable_density k).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (density_pos k hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

end ManuscriptChain.Hyperbolic
