import Zetahyperbolic.Section6.BetaOddRoot
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Unconditional convergence of the actual odd-beta rational Padé roots

The inverse-Gram formula and a two-vector Cauchy inequality bound the root
error by the last diagonal moment. This proves convergence for every k,N,
with an explicit polynomial error bound. It does not assert the stronger
geometric asymptotic printed in 6.15.
-/
noncomputable section
open Matrix Filter
open scoped Topology

namespace ManuscriptChain.BetaOddRoot
open BetaOddMoments BetaOddGram

theorem inverse_quadratic_diagonal_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (v : Fin n → ℝ) (i : Fin n) :
    (v i)^2 ≤ A i i * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by
  let e : Fin n → ℝ := Pi.single i 1
  let w : Fin n → ℝ := A⁻¹ *ᵥ v
  have hw : A *ᵥ w = v := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.one_mulVec]
  have hee : e ⬝ᵥ (A *ᵥ e) = A i i := by
    simp [e, Matrix.mulVec_single]
  have hew : e ⬝ᵥ (A *ᵥ w) = v i := by
    rw [hw]
    simp [e]
  have hs : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have hwe : w ⬝ᵥ (A *ᵥ e) = v i := by
    rw [← hs, Matrix.dotProduct_transpose_mulVec]
    exact hew
  have hww : w ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w := by
    rw [hw, dotProduct_comm]
  have hp (t : ℝ) : 0 ≤ A i i * (t*t) + (2*v i)*t + v ⬝ᵥ w := by
    have h := hA.posSemidef.dotProduct_mulVec_nonneg (t • e + w)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hee, hew, hwe, hww] at h
    nlinarith [h]
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  change (v i)^2 ≤ A i i * (v ⬝ᵥ w)
  nlinarith

theorem root_error_le_diagonal (k N h : ℕ) (hh : 0<h) (i : Fin h) :
    |moment k 0-root k N h| ≤ pencil k N h (moment k 0) i i := by
  have hb := inverse_quadratic_diagonal_bound (pencil k N h (moment k 0))
    (actual_beta_gram_posDef k N h) (alternatingVector h) i
  have hv : (alternatingVector h i)^2 = 1 := by
    change ((-1:ℝ)^i.val)^2 = 1
    rw [← pow_mul, Nat.mul_comm i.val 2, pow_mul]
    norm_num
  rw [hv] at hb
  rw [root_error k N h hh, inv_eq_one_div]
  apply (div_le_iff₀ (inverseGram_pos k N h hh)).2
  exact hb

theorem root_error_le_last_moment (k N h : ℕ) :
    |moment k 0-root k N (h+1)| ≤ moment k (2*(N+2*h)) := by
  let i : Fin (h+1) := ⟨h, by omega⟩
  have hb := root_error_le_diagonal k N (h+1) (by omega) i
  have he : pencil k N (h+1) (moment k 0) i i = moment k (2*(N+2*h)) := by
    rw [even_moment k (N+2*h)]
    simp only [pencil, i]
    rw [show N+h+h = N+2*h by omega]
  rwa [he] at hb

theorem root_error_explicit_bound (k N h : ℕ) :
    |moment k 0-root k N (h+1)| ≤
      1 / (((2*(N+2*h):ℕ):ℝ)+1)^(2*k+1) :=
  (root_error_le_last_moment k N h).trans (moment_bounds k (2*(N+2*h))).2

/-- The explicitly rational sequence converges to the actual beta value. -/
theorem rationalRoot_tendsto_beta (k N : ℕ) :
    Tendsto (fun h : ℕ => (rationalRoot k N (h+1) : ℝ)) atTop (𝓝 (moment k 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hi : Tendsto (fun h : ℕ => 2*(N+2*h)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hlim := (moment_tendsto_zero k).comp hi
  have hz := squeeze_zero
    (fun h => abs_nonneg (moment k 0-root k N (h+1)))
    (root_error_le_last_moment k N) hlim
  have he (h : ℕ) : ‖(rationalRoot k N (h+1) : ℝ)-moment k 0‖ =
      |moment k 0-root k N (h+1)| := by
    rw [← root_eq_rationalRoot k N (h+1) (by omega), Real.norm_eq_abs, abs_sub_comm]
  simpa only [he] using hz

end ManuscriptChain.BetaOddRoot
