import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
namespace ManuscriptChain.Beukers.Mellin

/-- Matrix of the four actual partial derivatives of (u^y,u^(1-y)). -/
def fiberJacobian (u y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![deriv (fun x : ℝ => x^y) u, deriv (fun t : ℝ => u^t) y;
    deriv (fun x : ℝ => x^(1-y)) u, deriv (fun t : ℝ => u^(1-t)) y]

theorem fiberJacobian_eq {u : ℝ} (hu : 0 < u) (y : ℝ) :
    fiberJacobian u y =
      !![y*u^(y-1), u^y*Real.log u;
        (1-y)*u^(-y), -(u^(1-y)*Real.log u)] := by
  have h₁ := (Real.hasDerivAt_rpow_const (x := u) (p := y) (Or.inl (ne_of_gt hu))).deriv
  have h₂ := ((hasDerivAt_id y).const_rpow hu).deriv
  have h₃ := (Real.hasDerivAt_rpow_const (x := u) (p := 1-y) (Or.inl (ne_of_gt hu))).deriv
  have h₄ := (((hasDerivAt_id y).const_sub 1).const_rpow hu).deriv
  simp only [id_eq, mul_one] at h₂ h₄
  have he : (1-y)-1 = -y := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fiberJacobian, h₁, h₂, h₃, h₄, he] <;> ring

theorem fiberJacobian_det {u : ℝ} (hu : 0 < u) (y : ℝ) :
    (fiberJacobian u y).det = -Real.log u := by
  have h₁ : u^(y-1) * u^(1-y) = 1 := by
    rw [← Real.rpow_add hu, show y-1+(1-y) = 0 by ring, Real.rpow_zero]
  have h₂ : u^y * u^(-y) = 1 := by
    rw [← Real.rpow_add hu, add_neg_cancel, Real.rpow_zero]
  simp only [fiberJacobian_eq hu, Matrix.det_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  calc
    y*u^(y-1) * -(u^(1-y)*Real.log u) -
        u^y*Real.log u*((1-y)*u^(-y)) =
      -y * (u^(y-1)*u^(1-y))*Real.log u -
        (1-y)*(u^y*u^(-y))*Real.log u := by ring
    _ = -Real.log u := by rw [h₁, h₂]; ring

theorem fiberJacobian_abs_det {u : ℝ} (hu : u ∈ Set.Ioo 0 1) (y : ℝ) :
    |(fiberJacobian u y).det| = -Real.log u := by
  rw [fiberJacobian_det hu.1, abs_of_pos (neg_pos.mpr (Real.log_neg hu.1 hu.2))]

theorem fiber_product {u : ℝ} (hu : 0 < u) (y : ℝ) :
    u^y * u^(1-y) = u := by
  rw [← Real.rpow_add hu, show y+(1-y) = 1 by ring, Real.rpow_one]

end ManuscriptChain.Beukers.Mellin
