import Zetahyperbolic.Section6.SecantMoments
import Zetahyperbolic.Section3.ConcreteMomentMeasure

/-!
# Actual rational-kernel Gram matrices for the accelerated secant density

This constructs the literal positive integral in 6.13(2) at every weight,
kernel parameter and finite dimension. The measure and all moment
integrability obligations are proved. Identification with the manuscript's
coupled beta functional, and its derivative matrix, are separate obligations.
The natural number `k` is the manuscript index minus one.
-/
noncomputable section
open MeasureTheory Set Polynomial Matrix

namespace ManuscriptChain.SecantGram
open CentralFactorialDecay CentralFactorialMoments

def weightedDensity (k N K m : ℕ) (u : ℝ) : ℝ :=
  Real.evalQ (Real.D N) (u ^ 2) ^ (2*m) /
    Real.evalQ (Real.D K) (u ^ 2) * density k u

theorem denominator_ge_one (K : ℕ) (u : ℝ) :
    1 ≤ Real.evalQ (Real.D K) (u^2) := by
  rw [ConcreteMoment.evalQ_D]
  apply Finset.one_le_prod
  intro j hj
  have hjR : (1:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  nlinarith [sq_nonneg u]

theorem weightedDensity_pos (k N K m : ℕ) {u : ℝ} (hu : 0 < u) :
    0 < weightedDensity k N K m u := by
  have hN := ConcreteMoment.evalQ_D_pos N (sq_pos_of_pos hu)
  have hK := denominator_ge_one K u
  exact mul_pos (div_pos (pow_pos hN _) (by linarith)) (density_pos k hu)

theorem weightedDensity_measurable (k N K m : ℕ) :
    Measurable (weightedDensity k N K m) := by
  unfold weightedDensity Real.evalQ
  apply Measurable.mul _ (density_measurable k)
  fun_prop

theorem integrableOn_polynomial_density (k : ℕ) (q : ℝ[X]) :
    IntegrableOn (fun u : ℝ => q.eval (u^2) * density k u) (Ioi 0) := by
  have hi := integrable_finsetSum q.support (fun e _ =>
    (integrableOn_monomial_density k (2*e)).const_mul (q.coeff e))
  apply hi.congr
  filter_upwards [] with u
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [← pow_mul]
  ring

theorem integrableOn_weighted_moment (k N K m e : ℕ) :
    IntegrableOn (fun u : ℝ => u^(2*e) * weightedDensity k N K m u) (Ioi 0) := by
  let q : ℝ[X] := Real.realPolynomial (Real.D N) ^ (2*m) * X^e
  have heval (u : ℝ) : q.eval (u^2) =
      Real.evalQ (Real.D N) (u^2) ^ (2*m) * u^(2*e) := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Real.evalQ, ← pow_mul]
  have hi := integrableOn_polynomial_density k q
  apply hi.mono' ((measurable_id.pow_const _).mul
    (weightedDensity_measurable k N K m)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hu.le _)
    (weightedDensity_pos k N K m hu).le), heval]
  have hN : 0 ≤ Real.evalQ (Real.D N) (u^2) ^ (2*m) :=
    pow_nonneg (ConcreteMoment.evalQ_D_pos N (sq_pos_of_pos hu)).le _
  have hb := div_le_self hN (denominator_ge_one K u)
  have hc := mul_le_mul_of_nonneg_right hb (density_pos k hu).le
  have hd := mul_le_mul_of_nonneg_left hc (pow_nonneg hu.le (2*e))
  simpa [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using hd

def weightedMeasure (k N K m : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun u => ENNReal.ofReal (weightedDensity k N K m u))

instance weightedMeasure_nullSingleton (k N K m : ℕ) :
    NullSingletonClass (weightedMeasure k N K m) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (k N K m : ℕ) : weightedMeasure k N K m ≠ 0 := by
  have hac : volume.restrict (Ioi (0:ℝ)) ≪ weightedMeasure k N K m := by
    apply withDensity_absolutelyContinuous'
      (weightedDensity_measurable k N K m).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_pos k N K m hu))
  intro hz
  rw [hz] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ univ) h
  simp at hu

def momentMeasure (k N K m : ℕ) : Measure ℝ :=
  (weightedMeasure k N K m).map (fun u : ℝ => u^2)

theorem momentMeasure_nonzero (k N K m : ℕ) : momentMeasure k N K m ≠ 0 :=
  (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero k N K m)

instance momentMeasure_nullSingleton (k N K m : ℕ) :
    NullSingletonClass (momentMeasure k N K m) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X^2-C t : ℝ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hc
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero
    (weightedMeasure k N K m)
  have hs : (fun u : ℝ => u^2) ⁻¹' {t} =
      {u | Polynomial.IsRoot (X^2-C t : ℝ[X]) u} := by
    ext u
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

theorem integral_moment (k N K m e : ℕ) :
    (∫ t, t^e ∂momentMeasure k N K m) =
      ∫ u in Ioi (0:ℝ), u^(2*e) * weightedDensity k N K m u := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (weightedDensity_measurable k N K m).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (weightedDensity_pos k N K m hu).le]
  simp only [smul_eq_mul]
  rw [← pow_mul]
  ring

theorem integrable_moment (k N K m e : ℕ) :
    Integrable (fun t : ℝ => t^e) (momentMeasure k N K m) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (weightedDensity_measurable k N K m).ennreal_ofReal (by simp)]
  apply (integrableOn_weighted_moment k N K m e).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [ENNReal.toReal_ofReal (weightedDensity_pos k N K m hu).le]
  simp only [Function.comp_def, smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Literal rational-kernel integral matrix, with arbitrary finite order. -/
def gram (k N K m h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∫ u in Ioi (0:ℝ), u^(2*(i.val+j.val)) *
    (Real.evalQ (Real.D N) (u^2) ^ (2*m) /
      Real.evalQ (Real.D K) (u^2) * density k u)

theorem gram_posDef (k N K m h : ℕ) : (gram k N K m h).PosDef := by
  have he : gram k N K m h = Moments.momentMatrix (momentMeasure k N K m) h := by
    ext i j
    exact (integral_moment k N K m (i.val+j.val)).symm
  rw [he]
  exact Moments.momentMatrix_posDef (momentMeasure_nonzero k N K m)
    (fun i j => integrable_moment k N K m (i.val+j.val))

theorem gram_det_pos (k N K m h : ℕ) : 0 < (gram k N K m h).det :=
  (gram_posDef k N K m h).det_pos

end ManuscriptChain.SecantGram
