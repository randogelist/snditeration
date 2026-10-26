import Zetahyperbolic.Section5.BeukersHilbertSchmidt
import Zetahyperbolic.Section5.KreinMonomial
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The actual Beukers–Krein identity for arbitrary real L² functions

The geometric expansion is integrated directly under the integrable majorant
`|f(x)g(y)| density(x,y)`. Square-integrability of the actual kernel supplies
that majorant by Hölder. No polynomial approximation or unproved tail premise
is needed. This proves the analytic component of 5.2(2), not the false fixed-K
cone assertion of 5.2(3).
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace ManuscriptChain.Beukers

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

/-- Actual Mellin-log coefficient of a function on the unit interval. -/
def l2KreinChannel (f : ℝ → ℝ) (m ν : ℕ) : ℝ :=
  ∫ x : ℝ in Ioo 0 1, f x * x ^ m * (-_root_.Real.log x) ^ ν

/-- The Mellin test functions are square-integrable, for every pair of orders. -/
theorem mellin_test_memLp_two (m ν : ℕ) :
    MemLp (fun x : ℝ => x ^ m * (-_root_.Real.log x) ^ ν) 2 unitMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using
    UnitLogMoments.integrable_pow_log (2 * m) (2 * ν)

/-- Every displayed Mellin coefficient of a real L² function is an honest
integral of an integrable function. -/
theorem l2_mellin_integrable {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure) (m ν : ℕ) :
    Integrable (fun x => f x * x ^ m * (-_root_.Real.log x) ^ ν) unitMeasure := by
  have h : MemLp (fun x => f x * (x ^ m * (-_root_.Real.log x) ^ ν)) 1 unitMeasure :=
    (mellin_test_memLp_two m ν).mul' hf
  simpa only [mul_assoc] using memLp_one_iff_integrable.mp h

/-- Products of two arbitrary L² functions are L² on the product square. -/
theorem l2_product_memLp_two {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) :
    MemLp (fun z : ℝ × ℝ => f z.1 * g z.2) 2 squareMeasure := by
  unfold squareMeasure
  rw [← Measure.prod_restrict]
  apply (memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd)).2
  simpa only [mul_pow] using hf.integrable_sq.mul_prod hg.integrable_sq

/-- Absolute integrability of the actual Beukers bilinear form for arbitrary L² inputs. -/
theorem l2_density_product_integrable {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) :
    Integrable (fun z : ℝ × ℝ => f z.1 * g z.2 * density z) squareMeasure := by
  exact memLp_one_iff_integrable.mp
    (show MemLp (fun z : ℝ × ℝ => f z.1 * g z.2 * density z) 1 squareMeasure from
      actual_density_memLp_two.mul' (l2_product_memLp_two hf hg))

private theorem momentTerm_zero_hasSum {z : ℝ × ℝ} (hz : z ∈ square) :
    HasSum (fun n => momentTerm 0 0 n z) (density z) := by
  have hu0 : 0 < z.1 * z.2 := mul_pos hz.1.1 hz.2.1
  have hu1 : z.1 * z.2 < 1 := by
    have h := mul_lt_mul_of_pos_right hz.1.2 hz.2.1
    nlinarith [hz.2.2]
  have hnorm : ‖z.1 * z.2‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_pos hu0]
  convert (hasSum_geometric_of_norm_lt_one hnorm).mul_left
    ((-_root_.Real.log (z.1 * z.2)) ^ 5 / 720) using 1
  · funext n
    rw [momentTerm_eq 0 0 n hz]
    simp only [pow_zero, one_mul]
    ring
  · unfold density
    field_simp [ne_of_gt (sub_pos.mpr hu1)]

private theorem l2_logMonomial_integrable {f : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (m ν : ℕ) :
    Integrable (fun x => f x * logMonomial m ν x) unitMeasure := by
  simpa only [logMonomial, mul_div_assoc, mul_assoc] using
    (l2_mellin_integrable hf m ν).div_const (ν.factorial : ℝ)

private theorem l2_momentTerm_expansion (f g : ℝ → ℝ) (m : ℕ) (z : ℝ × ℝ) :
    f z.1 * g z.2 * momentTerm 0 0 m z =
      (1 / 6 : ℝ) * ∑ ν : Fin 6,
        (f z.1 * logMonomial m ν.val z.1) *
          (g z.2 * logMonomial m (5 - ν.val) z.2) := by
  simp only [momentTerm, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

private theorem l2_momentTerm_integrable {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) (m : ℕ) :
    Integrable (fun z : ℝ × ℝ => f z.1 * g z.2 * momentTerm 0 0 m z)
      squareMeasure := by
  simp_rw [l2_momentTerm_expansion]
  apply Integrable.const_mul
  unfold squareMeasure
  rw [← Measure.prod_restrict]
  apply integrable_finsetSum
  intro ν _
  exact (l2_logMonomial_integrable hf m ν.val).mul_prod
    (l2_logMonomial_integrable hg m (5 - ν.val))

private theorem integral_l2_logMonomial (f : ℝ → ℝ) (m ν : ℕ) :
    (∫ x : ℝ in Ioo 0 1, f x * logMonomial m ν x) =
      l2KreinChannel f m ν / (ν.factorial : ℝ) := by
  simp only [logMonomial, mul_div_assoc, ← mul_assoc, integral_div, l2KreinChannel]

private theorem integral_l2_momentTerm {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) (m : ℕ) :
    (∫ z, f z.1 * g z.2 * momentTerm 0 0 m z ∂squareMeasure) =
      kreinSignedPairing (l2KreinChannel f m) (l2KreinChannel g m) := by
  simp_rw [l2_momentTerm_expansion]
  rw [integral_const_mul, integral_finsetSum]
  · have he (ν : Fin 6) :
        (∫ z, (f z.1 * logMonomial m ν.val z.1) *
          (g z.2 * logMonomial m (5-ν.val) z.2) ∂squareMeasure) =
          (l2KreinChannel f m ν.val / (ν.val.factorial : ℝ)) *
            (l2KreinChannel g m (5-ν.val) / ((5-ν.val).factorial : ℝ)) := by
      change (∫ z in square, _ ∂volume.prod volume) = _
      rw [setIntegral_prod_mul, integral_l2_logMonomial, integral_l2_logMonomial]
    simp_rw [he]
    rw [← kreinSix_eq_signed]
    norm_num [kreinSixPairing, Fin.sum_univ_succ]
    ring
  · intro ν _
    unfold squareMeasure
    rw [← Measure.prod_restrict]
    exact (l2_logMonomial_integrable hf m ν.val).mul_prod
      (l2_logMonomial_integrable hg m (5-ν.val))

/-- Convergent exact signed-channel decomposition for arbitrary real L² inputs. -/
theorem hasSum_l2_krein_pairing {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) :
    HasSum (fun m => kreinSignedPairing (l2KreinChannel f m) (l2KreinChannel g m))
      (∫ z, f z.1 * g z.2 * density z ∂squareMeasure) := by
  have hmajorant : Integrable (fun z : ℝ × ℝ => |f z.1 * g z.2| * density z)
      squareMeasure := by
    have h : MemLp (fun z : ℝ × ℝ => ‖f z.1 * g z.2‖ * density z) 1 squareMeasure :=
      actual_density_memLp_two.mul' (l2_product_memLp_two hf hg).norm
    simpa only [Real.norm_eq_abs] using memLp_one_iff_integrable.mp h
  have hseries : HasSum
      (fun m => ∫ z, f z.1 * g z.2 * momentTerm 0 0 m z ∂squareMeasure)
      (∫ z, f z.1 * g z.2 * density z ∂squareMeasure) := by
    apply hasSum_integral_of_dominated_convergence
      (fun m z => |f z.1 * g z.2| * momentTerm 0 0 m z)
    · intro m
      exact (l2_momentTerm_integrable hf hg m).aestronglyMeasurable
    · intro m
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      exact le_of_eq (by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (momentTerm_nonneg 0 0 m hz)])
    · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      exact ((momentTerm_zero_hasSum hz).mul_left _).summable
    · apply hmajorant.congr
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      exact ((momentTerm_zero_hasSum hz).mul_left _).tsum_eq.symm
    · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
      exact (momentTerm_zero_hasSum hz).mul_left _
  simpa only [integral_l2_momentTerm hf hg] using hseries

/-- Arbitrary-L² form of the actual Beukers–Krein integral identity. -/
theorem integral_l2_product_eq_krein_tsum {f g : ℝ → ℝ}
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) :
    (∫ z, f z.1 * g z.2 * density z ∂squareMeasure) =
      ∑' m, kreinSignedPairing (l2KreinChannel f m) (l2KreinChannel g m) :=
  (hasSum_l2_krein_pairing hf hg).tsum_eq.symm

/-- Integral of the displayed positive mode, with its integrability justified. -/
theorem l2_positive_mode_integral {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure)
    (m ν : ℕ) :
    (∫ x : ℝ in Ioo 0 1,
      f x * (x ^ m * ((-_root_.Real.log x) ^ ν +
        (-_root_.Real.log x) ^ (5-ν)))) =
      l2KreinChannel f m ν + l2KreinChannel f m (5-ν) := by
  simp only [mul_add, ← mul_assoc]
  exact integral_add (l2_mellin_integrable hf m ν)
    (l2_mellin_integrable hf m (5-ν))

/-- Integral of the displayed negative mode, with its integrability justified. -/
theorem l2_negative_mode_integral {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure)
    (m ν : ℕ) :
    (∫ x : ℝ in Ioo 0 1,
      f x * (x ^ m * ((-_root_.Real.log x) ^ ν -
        (-_root_.Real.log x) ^ (5-ν)))) =
      l2KreinChannel f m ν - l2KreinChannel f m (5-ν) := by
  simp only [mul_sub, ← mul_assoc]
  exact integral_sub (l2_mellin_integrable hf m ν)
    (l2_mellin_integrable hf m (5-ν))

/-- The exact analytic assertion of printed Theorem 5.2(2), for every real L²
function, using the actual density and actual integrals of the printed modes. -/
theorem theorem_5_2_l2_krein {f : ℝ → ℝ} (hf : MemLp f 2 unitMeasure) :
    (∫ z, f z.1 * f z.2 * density z ∂squareMeasure) =
      (1 / 1440 : ℝ) * ∑' m : ℕ, ∑ ν : Fin 3,
        (Nat.choose 5 ν.val : ℝ) *
          ((∫ x : ℝ in Ioo 0 1,
            f x * (x ^ m * ((-_root_.Real.log x) ^ ν.val +
              (-_root_.Real.log x) ^ (5-ν.val)))) ^ 2 -
           (∫ x : ℝ in Ioo 0 1,
            f x * (x ^ m * ((-_root_.Real.log x) ^ ν.val -
              (-_root_.Real.log x) ^ (5-ν.val)))) ^ 2) := by
  rw [integral_l2_product_eq_krein_tsum hf hf, ← tsum_mul_left]
  apply tsum_congr
  intro m
  simp only [kreinSignedPairing, l2_positive_mode_integral hf,
    l2_negative_mode_integral hf, pow_two]

/-- Mellin channels are independent of the representative of an L² class. -/
theorem l2KreinChannel_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[unitMeasure] g)
    (m ν : ℕ) : l2KreinChannel f m ν = l2KreinChannel g m ν := by
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- The actual bilinear integral is independent of both L² representatives. -/
theorem l2_integral_congr_ae {f f' g g' : ℝ → ℝ}
    (hff' : f =ᵐ[unitMeasure] f') (hgg' : g =ᵐ[unitMeasure] g') :
    (∫ z, f z.1 * g z.2 * density z ∂squareMeasure) =
      ∫ z, f' z.1 * g' z.2 * density z ∂squareMeasure := by
  apply integral_congr_ae
  unfold squareMeasure
  rw [← Measure.prod_restrict]
  filter_upwards [(quasiMeasurePreserving_fst (μ := unitMeasure) (ν := unitMeasure)).ae hff',
    (quasiMeasurePreserving_snd (μ := unitMeasure) (ν := unitMeasure)).ae hgg'] with z hz₁ hz₂
  rw [hz₁, hz₂]

end ManuscriptChain.Beukers
