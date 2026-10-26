import Zetahyperbolic

/-!
Experimental prerequisite ledger for printed Proposition 5.3.
SOURCE_ONLY_UNCOMPILED. Actual printed density and its geometric modes are
specified explicitly. No beta moment identity or hyperbolicity is assumed.
-/
noncomputable section
open MeasureTheory
namespace Experimental.P05_03

/-- The literal density of the supplied manuscript's Proposition 5.3. -/
def betaFourDensity (z : ℝ × ℝ) : ℝ :=
  (-Real.log (z.1 * z.2)) ^ 2 / (6 * (1 + z.1 ^ 2 * z.2 ^ 2))

/-- The alternating geometric term before integration. -/
def betaFourMode (k1 k2 n : ℕ) (z : ℝ × ℝ) : ℝ :=
  (1 / 6 : ℝ) * (-1 : ℝ) ^ n *
    z.1 ^ (4 * k1 + 2 * n) * z.2 ^ (4 * k2 + 2 * n) *
      (-Real.log (z.1 * z.2)) ^ 2

/-- Absolute integral summability needed for the series/integral passage.
This axiom does not identify the summed moment with beta(4). -/
axiom betaFour_modes_integral_norm_summable (k1 k2 : ℕ) :
  Summable (fun n : ℕ =>
    ∫ z, ‖betaFourMode k1 k2 n z‖ ∂ManuscriptChain.Beukers.squareMeasure)

-- Existing generic Mellin input is imported rather than axiomatized:
-- ManuscriptChain.UnitLogMoments.integral_pow_log
-- ManuscriptChain.UnitLogMoments.integrable_pow_log

end Experimental.P05_03
