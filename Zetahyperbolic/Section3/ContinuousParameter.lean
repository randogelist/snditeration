import Zetahyperbolic.Section3.ContinuousPencil
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Continuity of the real-weight family

The actual integral Gram entries vary continuously with the weight. Domination
uses the sum of two endpoint kernels; thus no unproved uniform-integrability
premise is inserted into the real-parameter pencil construction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Filter Topology

namespace ManuscriptChain.ContinuousWeight

lemma continuousAt_prefactor {s : ℝ} (hs : 0 < s) : ContinuousAt prefactor s := by
  have hg : ContinuousAt Real.Gamma s :=
    (Real.differentiableAt_Gamma (fun n => by
      intro he
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)).continuousAt
  exact (continuousAt_const.mul
    ((Real.continuous_const_rpow (by positivity)).continuousAt.comp
      (continuousAt_id.sub continuousAt_const))).div hg
        (ne_of_gt (Real.Gamma_pos_of_pos hs))

lemma continuous_exponentialTerm (n : ℕ) (y : ℝ) :
    Continuous (fun s => exponentialTerm s n y) := by
  unfold exponentialTerm
  exact ((Real.continuous_const_rpow (by positivity)).comp
    (continuous_id.sub continuous_const)).mul continuous_const

lemma continuousAt_exponentialSum (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun t => ∑' n, exponentialTerm t n y) s := by
  have hc : ContinuousOn (fun t => ∑' n, exponentialTerm t n y) (Iio (s+1)) := by
    apply continuousOn_tsum (fun n => (continuous_exponentialTerm n y).continuousOn)
      (summable_exponentialTerm (s+1) hy)
    intro n t ht
    rw [Real.norm_of_nonneg (exponentialTerm_pos t n y).le]
    unfold exponentialTerm
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      (by linarith [show t < s+1 from ht])
  exact hc.continuousAt (Iio_mem_nhds (by linarith))

def kernel (s y : ℝ) : ℝ := y ^ s * ∑' n, exponentialTerm s n y

lemma kernel_nonneg (s : ℝ) {y : ℝ} (hy : 0 < y) : 0 ≤ kernel s y := by
  exact mul_nonneg (Real.rpow_pos_of_pos hy _).le
    (tsum_nonneg (fun n => (exponentialTerm_pos s n y).le))

lemma continuousAt_kernel (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun t => kernel t y) s :=
  (Real.continuousAt_const_rpow hy.ne').mul (continuousAt_exponentialSum s hy)

lemma term_eq_product_power (s : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    y ^ s * exponentialTerm s n y =
      y * (y * ((n+1:ℕ):ℝ)) ^ (s-1) *
        Real.exp (-(2*Real.pi*y) * ((n+1:ℕ):ℝ)) := by
  have he : y ^ s = y ^ (s-1) * y := by
    calc
      _ = y ^ ((s-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hy, Real.rpow_one]
  rw [Real.mul_rpow hy.le (by positivity), he]
  unfold exponentialTerm
  ring

lemma power_le_endpoint_sum {a b t x : ℝ} (hx : 0 < x) (ha : a ≤ t) (hb : t ≤ b) :
    x ^ t ≤ x ^ a + x ^ b := by
  rcases le_total 1 x with hx1 | hx1
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_pos_of_pos hx _).le)
  · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 ha).trans
      (le_add_of_nonneg_right (Real.rpow_pos_of_pos hx _).le)

/-- A single pair of endpoint kernels dominates every intermediate exponent. -/
lemma kernel_le_endpoint_sum {a b s y : ℝ} (hy : 0 < y) (ha : a ≤ s) (hb : s ≤ b) :
    kernel s y ≤ kernel a y + kernel b y := by
  have hterm (n : ℕ) : y ^ s * exponentialTerm s n y ≤
      y ^ a * exponentialTerm a n y + y ^ b * exponentialTerm b n y := by
    rw [term_eq_product_power s n hy, term_eq_product_power a n hy,
      term_eq_product_power b n hy]
    have h := power_le_endpoint_sum (show 0 < y * ((n+1:ℕ):ℝ) by positivity)
      (show a-1 ≤ s-1 by linarith) (show s-1 ≤ b-1 by linarith)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hy.le)
      (Real.exp_pos (-(2*Real.pi*y) * ((n+1:ℕ):ℝ))).le
    simpa only [mul_add, add_mul] using hh
  unfold kernel
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((summable_exponentialTerm a hy).mul_left (y^a))
      ((summable_exponentialTerm b hy).mul_left (y^b))]
  exact ((summable_exponentialTerm s hy).mul_left (y^s)).tsum_le_tsum hterm
    (((summable_exponentialTerm a hy).mul_left (y^a)).add
      ((summable_exponentialTerm b hy).mul_left (y^b)))

def rationalWeight (p : Real.Parameters) (y : ℝ) : ℝ :=
  Real.evalQ (Real.D p.N ^ (2*p.m-1)) (y^2) / Real.evalQ (Real.tailD p) (y^2)

def momentKernel (p : Real.Parameters) (e : ℕ) (s y : ℝ) : ℝ :=
  y ^ (2*e) * rationalWeight p y * kernel s y

lemma rationalWeight_nonneg (p : Real.Parameters) {y : ℝ} (hy : 0 < y) :
    0 ≤ rationalWeight p y := by
  unfold rationalWeight
  apply div_nonneg _ (le_trans zero_le_one (ConcreteMoment.evalQ_tailD_ge_one p (sq_nonneg y)))
  have h := (ConcreteMoment.evalQ_D_pos p.N (show 0 < y^2 by positivity)).le
  simpa [Real.evalQ, Real.realPolynomial] using pow_nonneg h (2*p.m-1)

lemma momentKernel_nonneg (p : Real.Parameters) (e : ℕ) (s : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ momentKernel p e s y :=
  mul_nonneg (mul_nonneg (pow_nonneg hy.le _) (rationalWeight_nonneg p hy))
    (kernel_nonneg s hy)

lemma momentKernel_mul_prefactor (p : Real.Parameters) (e : ℕ) (s y : ℝ) :
    prefactor s * momentKernel p e s y = y^(2*e) * weightedDensity p s y := by
  unfold momentKernel rationalWeight kernel weightedDensity density
  ring

lemma integrableOn_momentKernel (p : Real.Parameters) (e : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (momentKernel p e s) (Ioi 0) := by
  have hi := (integrableOn_weightedDensity_moment p s hs e).div_const (prefactor s)
  apply hi.congr
  filter_upwards [] with y
  rw [← momentKernel_mul_prefactor, mul_div_cancel_left₀ _ (prefactor_pos hs).ne']

lemma continuousAt_momentKernel (p : Real.Parameters) (e : ℕ) (s : ℝ)
    {y : ℝ} (hy : 0 < y) : ContinuousAt (fun t => momentKernel p e t y) s :=
  continuousAt_const.mul (continuousAt_kernel s hy)

lemma momentKernel_le_endpoint_sum (p : Real.Parameters) (e : ℕ)
    {a b s y : ℝ} (hy : 0 < y) (ha : a ≤ s) (hb : s ≤ b) :
    momentKernel p e s y ≤ momentKernel p e a y + momentKernel p e b y := by
  have h := mul_le_mul_of_nonneg_left (kernel_le_endpoint_sum hy ha hb)
    (mul_nonneg (pow_nonneg hy.le (2*e)) (rationalWeight_nonneg p hy))
  simpa only [momentKernel, mul_add] using h

/-- Dominated convergence is proved from integrable endpoint kernels. -/
lemma continuousAt_integral_momentKernel (p : Real.Parameters) (e : ℕ)
    {s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun t => ∫ y : ℝ in Ioi 0, momentKernel p e t y) s := by
  let a := s/2
  let b := s+1
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hi : Ioo a b ∈ 𝓝 s := Ioo_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)
  apply continuousAt_of_dominated (bound := fun y => momentKernel p e a y + momentKernel p e b y)
  · filter_upwards [hi] with t ht
    exact (integrableOn_momentKernel p e (lt_trans ha ht.1)).aestronglyMeasurable
  · filter_upwards [hi] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_of_nonneg (momentKernel_nonneg p e t hy)]
    exact momentKernel_le_endpoint_sum p e hy ht.1.le ht.2.le
  · exact (integrableOn_momentKernel p e ha).add (integrableOn_momentKernel p e hb)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact continuousAt_momentKernel p e s hy

lemma gram_eq_prefactor_integral (p : Real.Parameters) {s : ℝ} (hs : 0 < s)
    (i j : Fin p.h) :
    gram p s i j = prefactor s * ∫ y : ℝ in Ioi 0, momentKernel p (i.val+j.val) s y := by
  rw [gram_integral p hs i j, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (momentKernel_mul_prefactor p (i.val+j.val) s y).symm

/-- The actual integral Gram matrix is continuous in the real weight. -/
theorem continuousAt_gram (p : Real.Parameters) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (gram p) s := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  apply ((continuousAt_prefactor hs).mul
    (continuousAt_integral_momentKernel p (i.val+j.val) hs)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  exact gram_eq_prefactor_integral p ht i j

end ManuscriptChain.ContinuousWeight
