import Zetahyperbolic.Section3.MixedMomentAllOrders
import Zetahyperbolic.Section3.MomentAndreief
import Zetahyperbolic.Section3.MomentProductSupport

/-!
# All-order arbitrary mixed-minor positivity for positive atomless measures

The exact integral determinant identity and generalized Vandermonde signs prove
strict positivity for unrelated increasing row and column index sequences.
Atomlessness makes almost every product-measure node vector collision-free.
This closes the total-positivity clause; measure uniqueness is a separate clause.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Matrix Filter

namespace ManuscriptChain.PositiveMomentMinors

private theorem evaluation_det_transpose {n : ℕ} (e : Fin n → ℕ) (x : Fin n → ℝ) :
    (MomentAndreief.evaluationMatrix (fun (i : Fin n) (t : ℝ) => t ^ e i) x).det =
      Matrix.det (fun i j : Fin n => x i ^ e j) := by
  rw [← Matrix.det_transpose]
  rfl

/-- Strict positivity for arbitrary increasing row and column exponents for
any nonzero atomless measure on the positive half-line with all moments finite. -/
theorem mixed_moment_det_pos (μ : Measure ℝ)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hμ : μ ≠ 0) (hμpos : ∀ᵐ t ∂μ, 0 < t)
    (hmom : ∀ r : ℕ, Integrable (fun t : ℝ => t^r) μ) {n : ℕ}
    (e f : Fin n → ℕ) (he : StrictMono e) (hf : StrictMono f) :
    0 < Matrix.det (fun i j : Fin n =>
      ∫ t, t ^ (e i + f j) ∂μ) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let F : Fin n → ℝ → ℝ := fun i t => t ^ e i
  let G : Fin n → ℝ → ℝ := fun i t => t ^ f i
  let H : (Fin n → ℝ) → ℝ := fun x =>
    (MomentAndreief.evaluationMatrix F x).det *
      (MomentAndreief.evaluationMatrix G x).det
  have hfg (i j : Fin n) : Integrable (fun t => F i t * G j t) μ := by
    simpa only [F, G, ← pow_add] using hmom (e i + f j)
  have hint : Integrable H ν := MomentAndreief.integrable_det_mul_det μ F G hfg
  have hpositive : ∀ᵐ x ∂ν, 0 < H x := by
    have hnodes : ∀ᵐ x ∂ν, ∀ i, 0 < x i :=
      MomentProductSupport.pi_ae_pos μ n hμpos
    filter_upwards [hnodes, MomentProductSupport.pi_ae_injective μ n] with x hxp hxi
    dsimp only [H, F, G]
    rw [evaluation_det_transpose, evaluation_det_transpose]
    exact MixedMomentAllOrders.generalized_vandermonde_product_pos e f he hf x hxi hxp
  have huniv : 0 < ν Set.univ :=
    Measure.measure_univ_pos.mpr (MomentProductSupport.pi_ne_zero μ n (hμ))
  have hsupport : ν (Function.support H)ᶜ = 0 := by
    apply (ae_iff).mp
    filter_upwards [hpositive] with x hx
    simpa only [Set.mem_compl_iff, Function.mem_support, not_not] using ne_of_gt hx
  have hI : 0 < ∫ x, H x ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpositive.mono (fun _ h => h.le)) hint).2
    rw [measure_of_measure_compl_eq_zero hsupport]
    exact huniv
  have hm : MomentAndreief.pairingMatrix μ F G =
      (fun i j : Fin n => ∫ t, t ^ (e i + f j) ∂μ) := by
    ext i j
    simp only [MomentAndreief.pairingMatrix, F, G, ← pow_add]
  have hid := MomentAndreief.integral_det_mul_det μ F G hfg
  have hmul : 0 < (n.factorial : ℝ) * Matrix.det (fun i j : Fin n =>
      ∫ t, t ^ (e i + f j) ∂μ) := by
    change 0 < ∫ x, (MomentAndreief.evaluationMatrix F x).det *
      (MomentAndreief.evaluationMatrix G x).det ∂Measure.pi (fun _ : Fin n => μ) at hI
    rw [hid, hm] at hI
    simpa only [Fintype.card_fin] using hI
  exact pos_of_mul_pos_right hmul (Nat.cast_nonneg _)

end ManuscriptChain.PositiveMomentMinors
