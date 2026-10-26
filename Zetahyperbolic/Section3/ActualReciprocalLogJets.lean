import Zetahyperbolic.Section3.ActualReciprocalHankel
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas


/-!
# First logarithmic derivative and its exact rational witness

The actual constructed determinant factorization gives P'/P = sum 1/(x-r).
Consequently the manuscript's opposite-gap convention sum 1/(r-x) has a
minus sign. At a rational non-root shift its witness is the rational number
-P'(q)/P(q). No spectral or Gram certificate is passed by the caller.

Higher logarithmic derivatives and rationality of every higher power sum are
separate assertions; this module establishes the first order exactly.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace LeanPaper.ReciprocalLogDerivative

open ManuscriptChain.Spectral
open LeanPaper.ReciprocalRootMoments

theorem factorization_logDeriv {n : ℕ} {p : SymmetricAffinePencil n}
    (c : RootFactorization p) (x : ℝ) (hx : p.detPolynomial.eval x ≠ 0) :
    logDeriv (fun t : ℝ => p.detPolynomial.eval t) x =
      ∑ i, (x - c.root i)⁻¹ := by
  have hroot (i : Fin n) : x ≠ c.root i := by
    intro heq
    apply hx
    rw [heq]
    exact c.eval_root i
  have hfac (i : Fin n) : 1 + (x - p.center) * c.beta i ≠ 0 := by
    intro hi
    exact hroot i ((linear_factor_eq_zero_iff p.center (c.beta i) x
      (c.beta_ne_zero i)).mp hi)
  have hd (i : Fin n) :
      HasDerivAt (fun t : ℝ => 1 + (t - p.center) * c.beta i) (c.beta i) x := by
    simpa [spectralFactor] using (spectralFactor p.center (c.beta i)).hasDerivAt x
  have heq : (fun t : ℝ => p.detPolynomial.eval t) =
      (fun t : ℝ => Matrix.det p.base * ∏ i, (1 + (t - p.center) * c.beta i)) := by
    funext t
    exact c.eval_eq t
  rw [heq, logDeriv_const_mul x _ c.base_det_ne_zero,
    logDeriv_prod (fun i _ => hfac i) (fun i _ => (hd i).differentiableAt)]
  apply Finset.sum_congr rfl
  intro i _
  rw [logDeriv_apply, (hd i).deriv]
  have hlinear : 1 + (x - p.center) * c.beta i = (x - c.root i) * c.beta i := by
    dsimp only [RootFactorization.root]
    field_simp [c.beta_ne_zero i]
    ring
  rw [hlinear]
  field_simp [c.beta_ne_zero i, sub_ne_zero.mpr (hroot i)]

theorem actual_logDeriv
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    logDeriv (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p)) x =
      ∑ i, (x - manuscriptRoots p hp i)⁻¹ := by
  have hc := factorization_logDeriv
    (ManuscriptChain.General.factorization p (ManuscriptChain.GRAM_POSITIVE p hp)) x
    (by simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial,
      ManuscriptChain.Real.evalQ] using hx)
  change logDeriv (fun t : ℝ =>
    (ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval t) x = _
  simpa only [ManuscriptChain.Real.manuscriptPencil_detPolynomial,
    manuscriptRoots] using hc

/-- This sign is the correction required by the printed r-x convention. -/
theorem actual_opposite_gap_sum
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    (∑ i, (manuscriptRoots p hp i - x)⁻¹) =
      -logDeriv (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p)) x := by
  rw [actual_logDeriv p hp x hx, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [show manuscriptRoots p hp i - x = -(x - manuscriptRoots p hp i) by ring,
    inv_neg]

theorem evalQ_at_rat (P : ℚ[X]) (q : ℚ) :
    ManuscriptChain.Real.evalQ P (q : ℝ) = ((P.eval q : ℚ) : ℝ) := by
  exact Polynomial.eval_map_apply (p := P) (Rat.castHom ℝ) q

theorem rational_logDeriv (P : ℚ[X]) (q : ℚ) :
    logDeriv (ManuscriptChain.Real.evalQ P) (q : ℝ) =
      ((P.derivative.eval q / P.eval q : ℚ) : ℝ) := by
  rw [logDeriv_apply]
  change deriv (fun x : ℝ => (P.map (Rat.castHom ℝ)).eval x) (q : ℝ) /
    ManuscriptChain.Real.evalQ P (q : ℝ) = _
  rw [Polynomial.deriv, Polynomial.derivative_map]
  rw [show (P.derivative.map (Rat.castHom ℝ)).eval (q : ℝ) =
      ((P.derivative.eval q : ℚ) : ℝ) from evalQ_at_rat P.derivative q,
    evalQ_at_rat P q]
  norm_cast

/-- The rational witness is computed from the actual rational polynomial. -/
theorem actual_first_inverse_gap_sum_rational
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (q : ℚ)
    (hq : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) (q : ℝ) ≠ 0) :
    (∑ i, (manuscriptRoots p hp i - (q : ℝ))⁻¹) =
      ((-(ManuscriptChain.Real.delta p).derivative.eval q /
        (ManuscriptChain.Real.delta p).eval q : ℚ) : ℝ) := by
  rw [actual_opposite_gap_sum p hp (q : ℝ) hq,
    rational_logDeriv (ManuscriptChain.Real.delta p) q]
  push_cast
  ring

/-- The real logarithm here is log of the absolute value in Mathlib's real
log convention. Its derivative is valid on either sign component of P. -/
theorem actual_log_hasDerivAt
    (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (x : ℝ)
    (hx : ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) x ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      Real.log (ManuscriptChain.Real.evalQ (ManuscriptChain.Real.delta p) t))
      (∑ i, (x - manuscriptRoots p hp i)⁻¹) x := by
  rw [← actual_logDeriv p hp x hx, logDeriv_apply]
  change HasDerivAt (fun t : ℝ => Real.log
    ((ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval t))
    (deriv (fun t : ℝ =>
      (ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval t) x /
      (ManuscriptChain.Real.realPolynomial (ManuscriptChain.Real.delta p)).eval x) x
  rw [Polynomial.deriv]
  exact ((ManuscriptChain.Real.realPolynomial
    (ManuscriptChain.Real.delta p)).hasDerivAt x).log hx

end LeanPaper.ReciprocalLogDerivative

#print axioms LeanPaper.ReciprocalLogDerivative.actual_first_inverse_gap_sum_rational
#print axioms LeanPaper.ReciprocalLogDerivative.actual_log_hasDerivAt



/-!
# Constructed rational witnesses for every logarithmic derivative

A pair of rational polynomials represents a rational function. Quotient-rule
differentiation constructs the next pair, without normalization or a supplied
derivative certificate. Starting at P'/P produces all iterated logarithmic
derivatives on the nonzero locus of P. At a rational point every pair evaluates
to an explicit rational number.
-/

noncomputable section
open scoped Topology
open Filter Polynomial

namespace LeanPaper.RationalLogJets

open ManuscriptChain
open LeanPaper.ReciprocalLogDerivative

def jetStep (J : ℚ[X] × ℚ[X]) : ℚ[X] × ℚ[X] :=
  (J.1.derivative * J.2 - J.1 * J.2.derivative, J.2 ^ 2)

def logJet (P : ℚ[X]) : ℕ → ℚ[X] × ℚ[X]
  | 0 => (P.derivative, P)
  | n + 1 => jetStep (logJet P n)

def jetValue (J : ℚ[X] × ℚ[X]) (x : ℝ) : ℝ :=
  Real.evalQ J.1 x / Real.evalQ J.2 x

def rationalJetValue (J : ℚ[X] × ℚ[X]) (q : ℚ) : ℚ :=
  J.1.eval q / J.2.eval q

theorem evalQ_hasDerivAt (P : ℚ[X]) (x : ℝ) :
    HasDerivAt (Real.evalQ P) (Real.evalQ P.derivative x) x := by
  change HasDerivAt (fun y : ℝ => (P.map (Rat.castHom ℝ)).eval y)
    ((P.derivative.map (Rat.castHom ℝ)).eval x) x
  simpa only [Polynomial.derivative_map] using (P.map (Rat.castHom ℝ)).hasDerivAt x

theorem jetStep_hasDerivAt (J : ℚ[X] × ℚ[X]) (x : ℝ)
    (hx : Real.evalQ J.2 x ≠ 0) :
    HasDerivAt (jetValue J) (jetValue (jetStep J) x) x := by
  change HasDerivAt (fun y : ℝ => Real.evalQ J.1 y / Real.evalQ J.2 y) _ x
  have hh := (evalQ_hasDerivAt J.1 x).fun_div (evalQ_hasDerivAt J.2 x) hx
  simpa only [jetValue, jetStep, Real.evalQ, Real.realPolynomial,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] using hh

theorem logJet_denominator_ne_zero (P : ℚ[X]) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ P x ≠ 0) : Real.evalQ (logJet P n).2 x ≠ 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      simpa only [logJet, jetStep, Real.evalQ, Real.realPolynomial,
        Polynomial.map_pow, Polynomial.eval_pow] using pow_ne_zero 2 ih

theorem logJet_zero_eq (P : ℚ[X]) :
    jetValue (logJet P 0) = logDeriv (Real.evalQ P) := by
  funext x
  change Real.evalQ P.derivative x / Real.evalQ P x =
    deriv (Real.evalQ P) x / Real.evalQ P x
  rw [(evalQ_hasDerivAt P x).deriv]

/-- Every iterated logarithmic derivative is the value of the recursively
constructed rational pair. The sole domain hypothesis is P(x) != 0. -/
theorem iterated_logDeriv_eq_jet (P : ℚ[X]) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ P x ≠ 0) :
    iteratedDeriv n (logDeriv (Real.evalQ P)) x = jetValue (logJet P n) x := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero, logJet_zero_eq]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hh := jetStep_hasDerivAt (logJet P n) x (logJet_denominator_ne_zero P n x hx)
      have heq : iteratedDeriv n (logDeriv (Real.evalQ P)) =ᶠ[𝓝 x]
          jetValue (logJet P n) := by
        have hevent := (evalQ_hasDerivAt P x).continuousAt.eventually_ne hx
        filter_upwards [hevent] with y hy
        exact ih y hy
      exact (hh.congr_of_eventuallyEq heq).deriv

theorem jetValue_at_rat (J : ℚ[X] × ℚ[X]) (q : ℚ) :
    jetValue J (q : ℝ) = (rationalJetValue J q : ℝ) := by
  simp only [jetValue, rationalJetValue, evalQ_at_rat, Rat.cast_div]

theorem iterated_logDeriv_rational (P : ℚ[X]) (n : ℕ) (q : ℚ)
    (hq : Real.evalQ P (q : ℝ) ≠ 0) :
    iteratedDeriv n (logDeriv (Real.evalQ P)) (q : ℝ) =
      (rationalJetValue (logJet P n) q : ℝ) := by
  rw [iterated_logDeriv_eq_jet P n (q : ℝ) hq, jetValue_at_rat]

/-- The jet identity concerns actual iterated derivatives of log|P|, not a
formal sequence merely named logarithmic derivatives. -/
theorem iterated_log_eq_logDeriv (P : ℚ[X]) (n : ℕ) (x : ℝ)
    (hx : Real.evalQ P x ≠ 0) :
    iteratedDeriv (n + 1) (fun y : ℝ => _root_.Real.log (Real.evalQ P y)) x =
      iteratedDeriv n (logDeriv (Real.evalQ P)) x := by
  rw [iteratedDeriv_succ']
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hevent := (evalQ_hasDerivAt P x).continuousAt.eventually_ne hx
  filter_upwards [hevent] with y hy
  rw [logDeriv_apply, (evalQ_hasDerivAt P y).deriv]
  exact ((evalQ_hasDerivAt P y).log hy).deriv

theorem iterated_log_rational (P : ℚ[X]) (n : ℕ) (q : ℚ)
    (hq : Real.evalQ P (q : ℝ) ≠ 0) :
    iteratedDeriv (n + 1) (fun y : ℝ => _root_.Real.log (Real.evalQ P y)) (q : ℝ) =
      (rationalJetValue (logJet P n) q : ℝ) := by
  rw [iterated_log_eq_logDeriv P n (q : ℝ) hq,
    iterated_logDeriv_rational P n q hq]

end LeanPaper.RationalLogJets

#print axioms LeanPaper.RationalLogJets.iterated_log_rational
