import Zetahyperbolic.Section3.MomentSquareRoot
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Determinacy from a genuine exponential neighbourhood

This supplies the analytic uniqueness bridge in the Stieltjes programme:
finite real measures whose MGFs exist near zero and whose moments agree
are equal. The proof uses equality of the actual analytic Taylor series,
continuation on the common vertical strip, and characteristic-function
uniqueness. Exponential integrability is an explicit premise here; deriving
it from the manuscript's factorial bounds is a separate remaining obligation.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ManuscriptChain.MomentDeterminacy

/-- Equality of all moments identifies the actual MGF on a neighbourhood of
zero, provided both exponential-integrability domains contain that point
in their interiors. -/
theorem mgf_eventuallyEq_of_moments {μ ν : Measure ℝ}
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hm : ∀ n : ℕ, (∫ x : ℝ, x ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂ν) :
    mgf id μ =ᶠ[𝓝 (0 : ℝ)] mgf id ν := by
  have hpμ := hasFPowerSeriesAt_mgf hμ
  have hpν := hasFPowerSeriesAt_mgf hν
  simp only [id_eq, zero_mul, Real.exp_zero, mul_one] at hpμ hpν
  simp_rw [hm] at hpμ
  filter_upwards [hpμ.eventually_hasSum_sub, hpν.eventually_hasSum_sub] with x hxμ hxν
  exact hxμ.unique hxν

/-- Moment equality and a common exponential neighbourhood imply measure
uniqueness. Finite measure mass need not be normalized to one. -/
theorem measure_eq_of_moments_of_exponential_neighbourhood
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : (0 : ℝ) ∈ interior (integrableExpSet id μ))
    (hν : (0 : ℝ) ∈ interior (integrableExpSet id ν))
    (hm : ∀ n : ℕ, (∫ x : ℝ, x ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂ν) :
    μ = ν := by
  let U : Set ℂ := {z | z.re ∈
    interior (integrableExpSet id μ) ∩ interior (integrableExpSet id ν)}
  have hA : AnalyticOnNhd ℂ (complexMGF id μ) U :=
    fun z hz => analyticAt_complexMGF hz.1
  have hB : AnalyticOnNhd ℂ (complexMGF id ν) U :=
    fun z hz => analyticAt_complexMGF hz.2
  have hU : IsPreconnected U :=
    ((convex_integrableExpSet (X := id) (μ := μ)).interior.inter
      (convex_integrableExpSet (X := id) (μ := ν)).interior).linear_preimage
        Complex.reLm |>.isPreconnected
  have hzero : (0 : ℂ) ∈ U := by exact ⟨hμ, hν⟩
  have hlocal := mgf_eventuallyEq_of_moments hμ hν hm
  have hreal : ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ),
      complexMGF id μ (x : ℂ) = complexMGF id ν (x : ℂ) := by
    have he : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), mgf id μ x = mgf id ν x :=
      hlocal.filter_mono nhdsWithin_le_nhds
    apply he.frequently.mono
    intro x hx
    rw [complexMGF_ofReal, complexMGF_ofReal, hx]
  have hcomplex : ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      complexMGF id μ z = complexMGF id ν z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx, he⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, he⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · simpa only [Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx.1
    · simpa using hx.2
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    hA hB hU hzero hcomplex
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  apply heq
  simpa [U] using And.intro hμ hν

end ManuscriptChain.MomentDeterminacy
