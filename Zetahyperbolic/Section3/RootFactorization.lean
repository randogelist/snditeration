import Zetahyperbolic.Section3.ConcretePencil
import Mathlib

/-!
# Theorem 3.1: spectral factor algebra

Formal algebra of the roots r_i = center - (beta_i)⁻¹.
An arbitrary RootFactorization is *not* assumed for the final theorem:
a later Hermitian spectral step constructs it from a positive definite
Gram matrix and nonsingular direction.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Spectral

def spectralFactor (center beta : ℝ) : ℝ[X] :=
  1 + (X - C center) * C beta

structure RootFactorization {n : ℕ} (p : SymmetricAffinePencil n) where
  beta : Fin n → ℝ
  beta_ne_zero : ∀ i, beta i ≠ 0
  base_det_ne_zero : Matrix.det p.base ≠ 0
  factorization : p.detPolynomial =
    C (Matrix.det p.base) * ∏ i, spectralFactor p.center (beta i)

theorem linear_factor_eq_zero_iff {K : Type*} [Field K]
    (center beta x : K) (hb : beta ≠ 0) :
    1 + (x - center) * beta = 0 ↔ x = center - beta⁻¹ := by
  constructor
  · intro h
    have hmul : (x - center) * beta = -1 := by
      calc
        (x - center) * beta = (1 + (x - center) * beta) - 1 := by ring
        _ = -1 := by rw [h]; ring
    have hdiff : x - center = -(beta⁻¹) := by
      calc
        x - center = ((x - center) * beta) * beta⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hb, mul_one]
        _ = -(beta⁻¹) := by rw [hmul]; ring
    calc
      x = (x - center) + center := by ring
      _ = -(beta⁻¹) + center := by rw [hdiff]
      _ = center - beta⁻¹ := by ring
  · intro h
    rw [h]
    calc
      1 + (center - beta⁻¹ - center) * beta = 1 - beta⁻¹ * beta := by ring
      _ = 0 := by rw [inv_mul_cancel₀ hb]; ring

@[simp] theorem eval_spectralFactor (center beta x : ℝ) :
    (spectralFactor center beta).eval x = 1 + (x - center) * beta := by
  simp [spectralFactor]

theorem spectralFactor_ne_zero (center beta : ℝ) : spectralFactor center beta ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval center) h
  simp at he

theorem natDegree_spectralFactor (center beta : ℝ) (hb : beta ≠ 0) :
    (spectralFactor center beta).natDegree = 1 := by
  have heq : spectralFactor center beta = C beta * X + C (1 - center * beta) := by
    simp only [spectralFactor, map_sub, map_one, map_mul]
    ring
  rw [heq]
  exact Polynomial.natDegree_linear hb

namespace RootFactorization

variable {n : ℕ} {p : SymmetricAffinePencil n} (c : RootFactorization p)

include c

def root (i : Fin n) : ℝ := p.center - (c.beta i)⁻¹

theorem eval_eq (x : ℝ) :
    p.detPolynomial.eval x = Matrix.det p.base *
      ∏ i, (1 + (x - p.center) * c.beta i) := by
  rw [c.factorization]
  simp [Polynomial.eval_prod]

theorem center_nonvanishing : p.detPolynomial.eval p.center ≠ 0 := by
  simpa using c.base_det_ne_zero

theorem determinant_center_nonvanishing : p.detValue p.center ≠ 0 := by
  simpa [SymmetricAffinePencil.detValue] using c.base_det_ne_zero

theorem polynomial_ne_zero : p.detPolynomial ≠ 0 := by
  intro h
  apply c.center_nonvanishing
  rw [h]
  simp

theorem natDegree_eq : p.detPolynomial.natDegree = n := by
  rw [c.factorization, Polynomial.natDegree_C_mul c.base_det_ne_zero]
  have hprod := Polynomial.natDegree_prod (s := Finset.univ)
    (fun i : Fin n => spectralFactor p.center (c.beta i))
    (fun i _ => spectralFactor_ne_zero p.center (c.beta i))
  simpa [natDegree_spectralFactor, c.beta_ne_zero] using hprod

end RootFactorization
end ManuscriptChain.Spectral
