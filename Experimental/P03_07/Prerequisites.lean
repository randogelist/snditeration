import Zetahyperbolic

/-!
Experimental boundary for the original Theorem 3.7.
These are aliases of already-proved upstream facts, not new assumptions.
Individual nonvanishing of every centered coefficient is deliberately absent.
This new module is SOURCE_ONLY_UNCOMPILED.
-/

noncomputable section
open Polynomial

namespace Experimental.P03_07

abbrev actualPolynomial :=
  ManuscriptChain.NewtonTuran.Actual.primitiveRealPolynomial

theorem actual_real_splitting (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    (actualPolynomial p).Splits :=
  ManuscriptChain.NewtonTuran.Actual.primitiveRealPolynomial_splits p hp

theorem actual_center_nonzero (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) :
    (actualPolynomial p).eval (ManuscriptChain.Real.zeta p.weight) ≠ 0 :=
  ManuscriptChain.NewtonTuran.Actual.primitiveRealPolynomial_center_ne_zero p hp

theorem actual_two_distinct_roots (p : ManuscriptChain.Real.Parameters)
    (hp : ManuscriptChain.Real.Admissible p) (hh : 2 ≤ p.h) :
    ManuscriptChain.NewtonTuran.DerivativeDistinctRoots.HasDistinctRoots
      (actualPolynomial p) :=
  ManuscriptChain.NewtonTuran.Actual.actual_primitive_hasDistinctRoots p hp hh

end Experimental.P03_07
