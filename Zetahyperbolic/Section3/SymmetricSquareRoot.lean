import Zetahyperbolic.Section3.MomentSquareRoot
import Zetahyperbolic.Section3.MomentDeterminacy
import Zetahyperbolic.Section3.ExponentialMoment
import Zetahyperbolic.Section3.PrintedMomentMeasure

/-! Symmetric square-root coordinates for the Stieltjes moment problem.
The lift is constructed explicitly; odd moments vanish, even moments are
the original moments, and squaring recovers the original measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory Module
open scoped ENNReal Topology

namespace ManuscriptChain.SymmetricSquareRoot

def symmetrize (μ : Measure ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • (μ + μ.map (fun x : ℝ => -x))

def lift (μ : Measure ℝ) : Measure ℝ :=
  symmetrize (μ.map _root_.Real.sqrt)

instance symmetrize_isFiniteMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (symmetrize μ) := by
  constructor
  rw [symmetrize, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)

instance lift_isFiniteMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (lift μ) := by
  unfold lift
  infer_instance

theorem map_sq_symmetrize (μ : Measure ℝ) :
    (symmetrize μ).map (fun x : ℝ => x^2) = μ.map (fun x : ℝ => x^2) := by
  unfold symmetrize
  rw [Measure.map_smul, Measure.map_add _ _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hn : (fun x : ℝ => x^2) ∘ (fun x : ℝ => -x) = (fun x : ℝ => x^2) := by
    funext x
    simp
  rw [hn, smul_add, ← add_smul]
  norm_num

theorem map_sq_lift (μ : Measure ℝ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) :
    (lift μ).map (fun x : ℝ => x^2) = μ := by
  rw [lift, map_sq_symmetrize, MomentSquareRoot.map_sq_map_sqrt μ hμ]

private theorem neg_pow_even (x : ℝ) (n : ℕ) : (-x)^(2*n) = x^(2*n) := by
  simp [pow_mul]

private theorem neg_pow_odd (x : ℝ) (n : ℕ) : (-x)^(2*n+1) = -(x^(2*n+1)) := by
  simp [pow_add, pow_mul]

theorem integral_even_symmetrize (μ : Measure ℝ) (n : ℕ)
    (hi : Integrable (fun x : ℝ => x^(2*n)) μ) :
    (∫ x : ℝ, x^(2*n) ∂symmetrize μ) = ∫ x : ℝ, x^(2*n) ∂μ := by
  have hn : Integrable (fun x : ℝ => x^(2*n)) (μ.map (fun x : ℝ => -x)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    simpa only [Function.comp_apply, neg_pow_even] using hi
  unfold symmetrize
  rw [integral_smul_measure, integral_add_measure hi hn,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [neg_pow_even]
  norm_num <;> ring

theorem integral_odd_symmetrize (μ : Measure ℝ) (n : ℕ)
    (hi : Integrable (fun x : ℝ => x^(2*n+1)) μ) :
    (∫ x : ℝ, x^(2*n+1) ∂symmetrize μ) = 0 := by
  have hn : Integrable (fun x : ℝ => x^(2*n+1)) (μ.map (fun x : ℝ => -x)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    simpa only [Function.comp_apply, neg_pow_odd] using hi.neg
  unfold symmetrize
  rw [integral_smul_measure, integral_add_measure hi hn,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [neg_pow_odd, integral_neg, add_neg_cancel, smul_zero]

theorem integrable_even_sqrt (μ : Measure ℝ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (n : ℕ) (hi : Integrable (fun t : ℝ => t^n) μ) :
    Integrable (fun x : ℝ => x^(2*n)) (μ.map _root_.Real.sqrt) := by
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  apply hi.congr
  filter_upwards [hμ] with t ht
  simp only [Function.comp_apply, pow_mul, _root_.Real.sq_sqrt ht]

theorem integrable_pow_sqrt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ)
    (hi : Integrable (fun t : ℝ => t^n) μ) :
    Integrable (fun x : ℝ => x^n) (μ.map _root_.Real.sqrt) := by
  have he := integrable_even_sqrt μ hμ n hi
  have hn : Integrable (fun x : ℝ => ‖x‖^(2*n)) (μ.map _root_.Real.sqrt) := by
    simpa only [norm_pow] using he.norm
  have hs := integrable_norm_pow_of_le (f := fun x : ℝ => x)
    (by fun_prop) (show n ≤ 2*n by omega) hn
  exact (integrable_norm_iff (by fun_prop)).mp (by simpa only [norm_pow] using hs)

theorem integral_even_lift (μ : Measure ℝ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (n : ℕ) (hi : Integrable (fun t : ℝ => t^n) μ) :
    (∫ x : ℝ, x^(2*n) ∂lift μ) = ∫ t : ℝ, t^n ∂μ := by
  rw [lift, integral_even_symmetrize _ n (integrable_even_sqrt μ hμ n hi),
    MomentSquareRoot.integral_even_map_sqrt μ hμ]

theorem integral_odd_lift (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (n : ℕ)
    (hi : Integrable (fun t : ℝ => t^(2*n+1)) μ) :
    (∫ x : ℝ, x^(2*n+1) ∂lift μ) = 0 :=
  integral_odd_symmetrize _ n (integrable_pow_sqrt μ hμ (2*n+1) hi)

/-- Matching Stieltjes moments give matching moments of the constructed
symmetric lifts in every order, not only the even orders. -/
theorem lift_moments_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (iμ : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (iν : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν)
    (n : ℕ) : (∫ x : ℝ, x^n ∂lift μ) = ∫ x : ℝ, x^n ∂lift ν := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hn : n = 2*k := by omega
    subst n
    rw [integral_even_lift μ hμ k (iμ k), integral_even_lift ν hν k (iν k), hm]
  · obtain ⟨k, hk⟩ := ho
    have hn : n = 2*k+1 := by omega
    subst n
    rw [integral_odd_lift μ hμ k (iμ _), integral_odd_lift ν hν k (iν _)]

/-- The remaining analytic premise is explicitly an exponential neighbourhood
of each constructed lift. No arbitrary measure identification is assumed. -/
theorem measure_eq_of_lift_exponential_neighbourhood
    {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (iμ : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (iν : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν)
    (eμ : (0 : ℝ) ∈ interior (integrableExpSet id (lift μ)))
    (eν : (0 : ℝ) ∈ interior (integrableExpSet id (lift ν))) : μ = ν := by
  have hl := MomentDeterminacy.measure_eq_of_moments_of_exponential_neighbourhood
    eμ eν (lift_moments_eq hμ hν iμ iν hm)
  have hs := congrArg (fun ρ : Measure ℝ => ρ.map (fun x : ℝ => x^2)) hl
  simpa only [map_sq_lift μ hμ, map_sq_lift ν hν] using hs

/-- Exponential integrability on the original square-root coordinate supplies
an actual neighbourhood of exponential integrability of the symmetric lift. -/
theorem lift_exponential_neighbourhood {μ : Measure ℝ}
    (he : Integrable (fun t : ℝ => _root_.Real.exp ((1/2 : ℝ) * _root_.Real.sqrt t)) μ) :
    (0 : ℝ) ∈ interior (integrableExpSet id (lift μ)) := by
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset]
  refine ⟨-(1/2 : ℝ), (1/2 : ℝ), by constructor <;> norm_num, ?_⟩
  intro s hs
  change Integrable (fun x : ℝ => _root_.Real.exp (s * x)) (lift μ)
  have hpos : Integrable (fun x : ℝ => _root_.Real.exp (s * x))
      (μ.map _root_.Real.sqrt) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    apply he.mono' (by fun_prop)
    filter_upwards with t
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hs.2.le (Real.sqrt_nonneg t)
  have hnegbase : Integrable (fun t : ℝ => _root_.Real.exp (s * -_root_.Real.sqrt t)) μ := by
    apply he.mono' (by fun_prop)
    filter_upwards with t
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hns : -s ≤ (1/2 : ℝ) := by linarith [hs.1]
    simpa only [neg_mul, mul_neg] using
      mul_le_mul_of_nonneg_right hns (Real.sqrt_nonneg t)
  have hneg : Integrable (fun x : ℝ => _root_.Real.exp (s * x))
      ((μ.map _root_.Real.sqrt).map (fun x : ℝ => -x)) := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hnegbase
  exact (integrable_add_measure.mpr ⟨hpos, hneg⟩).smul_measure (by norm_num)

/-- Stieltjes uniqueness under the proved shifted-factorial growth condition.
The competing measure must genuinely have every stated moment integrable. -/
theorem stieltjes_unique_of_factorial {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (iμ : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) μ)
    (iν : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) = ∫ t : ℝ, t^n ∂ν)
    {C : ℝ} (hC : 0 < C) (A : ℕ)
    (hb : ∀ n : ℕ, (∫ t : ℝ, t^n ∂μ) ≤ C * (Nat.factorial (2*n+A) : ℝ)) :
    μ = ν := by
  apply measure_eq_of_lift_exponential_neighbourhood hμ hν iμ iν hm
  · exact lift_exponential_neighbourhood
      (ExponentialMoment.integrable_exp_sqrt_of_factorial hμ iμ hC A hb)
  · apply lift_exponential_neighbourhood
    apply ExponentialMoment.integrable_exp_sqrt_of_factorial hν iν hC A
    intro n
    rw [← hm n]
    exact hb n

end ManuscriptChain.SymmetricSquareRoot

namespace ManuscriptChain.ConcreteMoment

/-- The actual manuscript moment measure is uniquely determined among finite
positive measures supported on the nonnegative half-line by all its moments. -/
theorem actual_stieltjes_measure_unique (p : Real.Parameters) (hp : Real.Admissible p)
    (ν : Measure ℝ)
    (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (iν : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂momentMeasure p) = ∫ t : ℝ, t^n ∂ν) :
    momentMeasure p = ν := by
  letI : IsFiniteMeasure ν :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa only [pow_zero] using iν 0)
  obtain ⟨C, hC, A, hb⟩ := actualMomentFactorialMajorant p hp
  apply SymmetricSquareRoot.stieltjes_unique_of_factorial
    (by filter_upwards [momentMeasure_ae_pos p] with t ht; exact ht.le)
    hν (integrable_moment p) iν hm hC A
  intro n
  exact (le_abs_self _).trans (hb n)

end ManuscriptChain.ConcreteMoment

namespace ManuscriptChain.PrintedMomentMeasure

/-- Determinacy for the literal manuscript density, using its already proved
equality with the actual moment realization. -/
theorem printed_stieltjes_measure_unique (p : Real.Parameters) (hp : Real.Admissible p)
    (ν : Measure ℝ) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (iν : ∀ n : ℕ, Integrable (fun t : ℝ => t^n) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, t^n ∂printedMeasure p 1) = ∫ t : ℝ, t^n ∂ν) :
    printedMeasure p 1 = ν := by
  have he : ConcreteMoment.momentMeasure p = printedMeasure p 1 :=
    realizationMeasure_eq_printed p hp
  rw [← he]
  apply ConcreteMoment.actual_stieltjes_measure_unique p hp ν hν iν
  intro n
  rw [he]
  exact hm n

end ManuscriptChain.PrintedMomentMeasure
