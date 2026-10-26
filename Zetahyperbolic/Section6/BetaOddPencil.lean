import Zetahyperbolic.Section6.BetaOddResidueSigns

/-!
# The rational odd-square beta(4) pencil

The polynomial moments use the even Euler numbers, defined by their usual
reciprocal-cosh recurrence. The pole values are the literal ones in (6.2).
The pencil is evaluated by polynomial division and the simple-pole residues.
Its slope is the actual positive odd-square residue matrix, independently of
the false continuous-weight calibration in Theorem 6.4(1).
-/

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace ManuscriptChain.BetaOddPencil
open BetaOddResidueSigns

/-- `eulerEven n` is the coefficient `(2n)! [z^(2n)] sech z`. -/
def eulerEven : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ i : Fin (n + 1),
      (Nat.choose (2 * (n + 1)) (2 * i.val) : ℤ) * eulerEven i.val
termination_by n => n
decreasing_by exact i.isLt

theorem eulerEven_first_four :
    eulerEven 0 = 1 ∧ eulerEven 1 = -1 ∧
      eulerEven 2 = 5 ∧ eulerEven 3 = -61 := by
  have h0 : eulerEven 0 = 1 := by rw [eulerEven]
  have h1 : eulerEven 1 = -1 := by
    rw [eulerEven]
    norm_num [Fin.sum_univ_succ, h0]
  have h2 : eulerEven 2 = 5 := by
    rw [eulerEven]
    norm_num [Fin.sum_univ_succ, h0, h1]
  have h3 : eulerEven 3 = -61 := by
    rw [eulerEven]
    norm_num [Fin.sum_univ_succ, h0, h1, h2]
  exact ⟨h0, h1, h2, h3⟩

def monomialMoment (e : ℕ) : ℚ :=
  (-1 : ℚ) ^ e * (eulerEven e : ℚ) / 4 ^ (e + 1) *
    (Nat.choose (2 * e + 3) 3 : ℚ)

def polynomialMoment (Q : ℚ[X]) : ℚ :=
  Q.sum fun e c => c * monomialMoment e

def betaHarmonic (j : ℕ) : ℚ :=
  ∑ n ∈ Finset.range j, (-1 : ℚ) ^ n / (2 * (n : ℚ) + 1) ^ 4

def poleValue (j : ℕ) (x : ℚ) : ℚ :=
  (2 * (j : ℚ) + 1) ^ 3 * (-1 : ℚ) ^ j * (x - betaHarmonic j) -
    1 / 6 + (-1 : ℚ) ^ j / (2 * (2 * (j : ℚ) + 1))

def numerator (N m i j : ℕ) : ℚ[X] :=
  oddPrefix N ^ (2 * m - 1) * X ^ (i + j)

def quotient (N K m i j : ℕ) : ℚ[X] :=
  numerator N m i j /ₘ tail N K

def residueCoefficient (N K m i j a : ℕ) : ℚ :=
  (numerator N m i j).eval (-oddSquare a) /
    (derivative (tail N K)).eval (-oddSquare a)

def entry (N K m i j : ℕ) (x : ℚ) : ℚ :=
  polynomialMoment (quotient N K m i j) +
    ∑ a : Fin (K - N), residueCoefficient N K m i j (N + a.val) *
      poleValue (N + a.val) x

def rationalMatrix (N K m : ℕ) (x : ℚ) :
    Matrix (Fin (K - N)) (Fin (K - N)) ℚ :=
  fun i j => entry N K m i.val j.val x

def constantMatrix (N K m : ℕ) :
    Matrix (Fin (K - N)) (Fin (K - N)) ℝ :=
  (rationalMatrix N K m 0).map (fun q => (q : ℝ))

def rationalSlope (N K m : ℕ) :
    Matrix (Fin (K - N)) (Fin (K - N)) ℚ :=
  fun i j => ∑ a : Fin (K - N),
    residue N K m (N + a.val) * (-oddSquare (N + a.val)) ^ (i.val + j.val)

theorem residueCoefficient_slope (N K m i j a : ℕ) :
    residueCoefficient N K m i j a *
      ((2 * (a : ℚ) + 1) ^ 3 * (-1 : ℚ) ^ a) =
      residue N K m a * (-oddSquare a) ^ (i + j) := by
  simp only [residueCoefficient, numerator, residue, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem entry_affine (N K m i j : ℕ) (x : ℚ) :
    entry N K m i j x = entry N K m i j 0 +
      x * ∑ a : Fin (K - N),
        residue N K m (N + a.val) *
          (-oddSquare (N + a.val)) ^ (i + j) := by
  unfold entry
  rw [Finset.mul_sum, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hs := residueCoefficient_slope N K m i j (N + a.val)
  dsimp [poleValue]
  linear_combination x * hs

theorem rationalMatrix_affine (N K m : ℕ) (x : ℚ) :
    rationalMatrix N K m x = rationalMatrix N K m 0 + x • rationalSlope N K m := by
  ext i j
  exact entry_affine N K m i.val j.val x

theorem rationalSlope_real_eq (N K m : ℕ) :
    (rationalSlope N K m).map (fun q => (q : ℝ)) = slope N K m := by
  ext i j
  simp only [rationalSlope, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_neg, BetaOddResidueSigns.slope,
    PaperAdvances.Corollary3_6_WeightedCorrected.weightedHankel, nodes]

theorem constantMatrix_symmetric (N K m : ℕ) :
    (constantMatrix N K m).IsSymm := by
  ext i j
  simp only [constantMatrix, Matrix.transpose_apply, Matrix.map_apply,
    rationalMatrix, entry, quotient, residueCoefficient, numerator, Nat.add_comm]

/-- Literal partial-fraction evaluation agrees with the real affine pencil. -/
theorem rationalMatrix_real_eq (N K m : ℕ) (x : ℚ) :
    (rationalMatrix N K m x).map (fun q => (q : ℝ)) =
      constantMatrix N K m + (x : ℝ) • slope N K m := by
  rw [rationalMatrix_affine]
  ext i j
  have hs := congrFun (congrFun (rationalSlope_real_eq N K m) i) j
  simpa only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Rat.cast_add, Rat.cast_mul, constantMatrix] using
    congrArg (fun t : ℝ => (rationalMatrix N K m 0 i j : ℝ) + (x : ℝ) * t) hs

def positivePencil (N K m : ℕ) (hm : 1 ≤ m) :
    DualSpectral.PositiveSlopePencil (K - N) where
  constant := constantMatrix N K m
  slope := slope N K m
  constant_symmetric := constantMatrix_symmetric N K m
  slope_posDef := slope_posDef N K m hm

/-- The exact finite beta pencil has a full real spectral factorization. -/
theorem betaPencil_factorization (N K m : ℕ) (hm : 1 ≤ m) :
    ∃ roots : Fin (K - N) → ℝ,
      (positivePencil N K m hm).detPolynomial =
        C (Matrix.det (slope N K m)) * ∏ i, (X + C (roots i)) :=
  DualSpectral.positiveSlopePencil_factorization_exists (positivePencil N K m hm)

theorem betaPencil_degree (N K m : ℕ) (hm : 1 ≤ m) :
    (positivePencil N K m hm).detPolynomial.natDegree = K - N :=
  DualSpectral.positiveSlopePencil_degree (positivePencil N K m hm)

theorem betaPencil_complex_roots_real (N K m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z
      (positivePencil N K m hm).detPolynomial = 0) : z.im = 0 :=
  DualSpectral.positiveSlopePencil_every_complex_root_real
    (positivePencil N K m hm) z hz

end ManuscriptChain.BetaOddPencil

#print axioms ManuscriptChain.BetaOddPencil.rationalMatrix_real_eq
#print axioms ManuscriptChain.BetaOddPencil.betaPencil_factorization
#print axioms ManuscriptChain.BetaOddPencil.betaPencil_degree
#print axioms ManuscriptChain.BetaOddPencil.betaPencil_complex_roots_real
