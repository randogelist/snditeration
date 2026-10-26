import Zetahyperbolic.Section6.BetaOddMoments
import Zetahyperbolic.Section3.MomentPositivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Actual positive beta-odd Hankel matrices

All k,N,h are arbitrary natural numbers. The actual density is on (0,1),
its square pushforward is constructed, and the required moment identities,
integrability, nonzero mass and atomlessness are proved. This establishes
the positive-definiteness clause of 6.15(2)(i), not arbitrary mixed-minor
strict total positivity or the proposed root asymptotics.
-/
noncomputable section
open MeasureTheory Set Polynomial Matrix
open scoped BigOperators

namespace ManuscriptChain.BetaOddGram
open BetaOddMoments

theorem integrand_pos (k m : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 < integrand k m x := by
  have hlog : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hx.1 hx.2)
  unfold integrand raw
  exact div_pos (div_pos (mul_pos (pow_pos hx.1 _) (pow_pos hlog _))
    (by positivity)) (by positivity)

theorem integrand_measurable (k m : ℕ) : Measurable (integrand k m) := by
  unfold integrand raw
  fun_prop

def weightedMeasure (k N : ℕ) : Measure ℝ :=
  unitMeasure.withDensity (fun x => ENNReal.ofReal (integrand k (2*N) x))

instance weightedMeasure_nullSingleton (k N : ℕ) :
    NullSingletonClass (weightedMeasure k N) := by
  unfold weightedMeasure unitMeasure
  infer_instance

theorem weightedMeasure_nonzero (k N : ℕ) : weightedMeasure k N ≠ 0 := by
  have hac : unitMeasure ≪ weightedMeasure k N := by
    apply withDensity_absolutelyContinuous' (integrand_measurable k (2*N)).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (integrand_pos k (2*N) hx))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ univ) h
  norm_num [unitMeasure] at hu

def momentMeasure (k N : ℕ) : Measure ℝ := (weightedMeasure k N).map (fun x : ℝ => x^2)

theorem momentMeasure_nonzero (k N : ℕ) : momentMeasure k N ≠ 0 :=
  (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero k N)

instance momentMeasure_nullSingleton (k N : ℕ) : NullSingletonClass (momentMeasure k N) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X^2-C t : ℝ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hc
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure k N)
  have hs : (fun x : ℝ => x^2) ⁻¹' {t} = {x | Polynomial.IsRoot (X^2-C t : ℝ[X]) x} := by
    ext x
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

private theorem weighted_power (k N e : ℕ) (x : ℝ) :
    integrand k (2*N) x * (x^2)^e = integrand k (2*(N+e)) x := by
  simp only [integrand, raw, ← pow_mul, Nat.mul_add, pow_add]
  ring

theorem integrable_moment (k N e : ℕ) :
    Integrable (fun t : ℝ => t^e) (momentMeasure k N) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (integrand_measurable k (2*N)).ennreal_ofReal (by simp)]
  apply (integrand_integrable k (2*(N+e))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [ENNReal.toReal_ofReal (integrand_pos k (2*N) hx).le]
  simp only [Function.comp_def, smul_eq_mul]
  exact (weighted_power k N e x).symm

theorem integral_moment (k N e : ℕ) :
    (∫ t, t^e ∂momentMeasure k N) = moment k (2*(N+e)) := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (integrand_measurable k (2*N)).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [ENNReal.toReal_ofReal (integrand_pos k (2*N) hx).le]
  simp only [smul_eq_mul]
  exact weighted_power k N e x

/-- The literal real beta-odd affine Hankel matrix of manuscript 6.15. -/
def pencil (k N h : ℕ) (X : ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => (-1:ℝ)^(N+i.val+j.val) * (X-betaPartialSum k (N+i.val+j.val))

/-- No moment, positivity or nondegeneracy hypothesis is supplied by the caller. -/
theorem actual_beta_gram_posDef (k N h : ℕ) : (pencil k N h (moment k 0)).PosDef := by
  have he : pencil k N h (moment k 0) = Moments.momentMatrix (momentMeasure k N) h := by
    ext i j
    rw [Moments.momentMatrix, integral_moment, even_moment]
    simp only [pencil, Nat.add_assoc]
  rw [he]
  exact Moments.momentMatrix_posDef (momentMeasure_nonzero k N)
    (fun i j => integrable_moment k N (i.val+j.val))

theorem actual_beta_gram_det_pos (k N h : ℕ) : 0 < (pencil k N h (moment k 0)).det :=
  (actual_beta_gram_posDef k N h).det_pos

/-- Exact derivative matrix of the actual beta Hankel pencil. -/
def slope (N h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => (-1:ℝ)^(N+i.val+j.val)

theorem pencil_affine (k N h : ℕ) (X Y : ℝ) :
    pencil k N h X = pencil k N h Y + (X-Y) • slope N h := by
  ext i j
  simp only [pencil, slope, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem slope_outer_product (N h : ℕ) : slope N h =
    Matrix.vecMulVec (fun i : Fin h => (-1:ℝ)^N * (-1:ℝ)^i.val)
      (fun j : Fin h => (-1:ℝ)^j.val) := by
  ext i j
  simp only [slope, Matrix.vecMulVec, Matrix.of_apply, pow_add]

theorem slope_rank_one (N h : ℕ) (hh : 0 < h) : (slope N h).rank = 1 := by
  have hu : (slope N h).rank ≤ 1 := by
    rw [slope_outer_product]
    exact Matrix.rank_vecMulVec_le _ _
  let i₀ : Fin h := ⟨0, hh⟩
  let B : Matrix (Fin 1) (Fin 1) ℝ :=
    (slope N h).submatrix (fun _ => i₀) (fun _ => i₀)
  have hb : B.det ≠ 0 := by
    rw [Matrix.det_fin_one]
    change (-1:ℝ)^(N+0+0) ≠ 0
    exact pow_ne_zero _ (by norm_num)
  have hr : B.rank = 1 := by
    simpa using Matrix.rank_of_det_ne_zero hb
  have hl := Matrix.rank_submatrix_le (slope N h) (fun _ : Fin 1 => i₀) (fun _ : Fin 1 => i₀)
  change B.rank ≤ (slope N h).rank at hl
  omega

end ManuscriptChain.BetaOddGram
