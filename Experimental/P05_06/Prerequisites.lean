import Zetahyperbolic

/-!
Experimental prerequisite ledger for printed Theorem 5.6.
SOURCE_ONLY_UNCOMPILED. Only analytic existence prerequisites are assumed.
The exact outer value, inner inequality, pole replacement and valuation
improvement remain separate targets and are not axioms of this module.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Experimental.P05_06

def alpha : ℝ := 3 / 40
def lambda : ℝ := 37 / 40
def heightParameter : ℝ := 49 / 40

def vTilde (y : ℝ) : ℝ := 1 - y * (Int.floor (1 / y) : ℝ)
def uTilde (y : ℝ) : ℝ := max 0 (alpha + vTilde y - y)
def tTilde (y : ℝ) : ℝ := min alpha (vTilde y) + uTilde y
def rTilde (y : ℝ) : ℝ := max 0 (29 / 20 - 3 * y)

def outerR (y : ℝ) : ℝ :=
  if y < 1 / 2 then
    9 * (1 - y) - 16 * alpha - 7 * tTilde y +
      min (rTilde y) (y + uTilde y)
  else if y < 1 then
    9 * (1 - y) - 8 * tTilde y +
      min (rTilde y) (y - alpha + uTilde y)
  else 0

def outerT (y : ℝ) : ℝ :=
  outerR y - 2 * lambda * (Int.floor (1 / y) : ℝ) +
    ∑ j ∈ Finset.range 7, max 0 (2 * lambda - ((j + 1 : ℕ) : ℝ) * y)

def poleCount (x z : ℝ) : ℝ :=
  (Int.floor (x - z) : ℝ) + (Int.floor (x + z) : ℝ) + 1

def innerB (x z : ℝ) : ℝ := 4 * poleCount (alpha * x) z
def innerT (x : ℝ) : ℝ := (Int.floor (2 * heightParameter * x) : ℝ)
def innerS (x : ℝ) : ℝ := heightParameter * x - innerT x / 2
def innerQ (x : ℝ) : ℝ := (Int.floor (2 * x) : ℝ)
def innerNplus (x : ℝ) : ℝ := x - innerQ x / 2

def innerGamma (x : ℝ) : ℝ :=
  (∫ z in Set.Ioo (0 : ℝ) (1 / 2),
    (innerT x - innerB x z) *
      (innerT x + innerB x z - poleCount x z - 7)) +
    innerS x * (2 * innerT x - innerQ x - 7) +
    max 0 (innerS x - innerNplus x)

def innerCorrection (x : ℝ) : ℝ :=
  2 * lambda * x * (Int.floor x : ℝ) -
    16 * lambda * x * (Int.floor (alpha * x) : ℝ) -
    2 * (Int.floor (2 * lambda * x) : ℝ) * lambda * x +
    (Int.floor (2 * lambda * x) : ℝ) *
      ((Int.floor (2 * lambda * x) : ℝ) + 1) / 2

def innerR (x : ℝ) : ℝ := -innerGamma x - innerCorrection x

/-- Regularity input for the literal outer finite-range integrand. -/
axiom outerT_integrable :
  IntegrableOn outerT (Set.Icc (1 / 3 : ℝ) (37 / 20))

/-- Absolute convergence input only; no claimed sign or numerical bound. -/
axiom inner_tail_integrable :
  IntegrableOn (fun x : ℝ => innerR x / x ^ 3) (Set.Ioi 20)

end Experimental.P05_06
