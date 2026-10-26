# Theorem 6.1: focused construction and correction

The active target is Theorem 6.1 of the supplied 21 October 2026 manuscript,
with original definitions and all prime, degree, polynomial and local-index
quantifiers retained. Proof mode and GitHub CI target are unchanged. No local
Lean execution, branch merge or branch deletion is authorized by this record.

## Literal correction

Part (3) concludes that no nonzero integral column combination can cancel the
leading seventh-order pole. This is false: the nonzero coefficient vector (p,0)
is divisible by p, and lowers every output pole to order at most six. The proof
printed in the manuscript itself establishes divisibility of both coefficients
by p, not equality to zero. The correct obstruction requires a primitive vector,
meaning at least one coefficient is a p-adic unit. Preserve the original as a
refuted clause; do not count the corrected theorem as a completed original.

The local arithmetic matrix is explicitly the affine pencil at X in Z_p. Its
real specialization at zeta(7) is not silently assigned a p-adic value.

## Implemented routes

- Part (1): actual partial derivatives and Jacobian determinant of (u^y,u^(1-y));
  literal inner fiber integrals; absolute integrability and finite polynomial
  linearity; actual Beukers measure integral equals its one-variable Mellin
  integral for every pair of rational polynomials of degree at most K.
- Part (2): transfer of the previously audited companion outer-prime valuation,
  plus all harmonic lower bounds in the outer window and actual integral
  identification in a single theorem. No harmonic or valuation hypothesis is
  assumed in place of a proof.
- Part (3), corrected: exact leading residue matrix/kernel, actual rational
  local determinant valuation -14 and primitive-vector noncancellation; extension
  to every p-integral Q_p evaluation, and an actual nonzero-vector counterexample.
  The scaled-entry congruence with the printed leading matrix is tracked separately
  until its proof and audit are complete.

## Verification ledger

- Source da5911e84c1a6574af5730635a3e8c234c0dd3ce: successful destination run
  40333840272, job 121609981060. Build 8,865 jobs; full transitive audit of
  2,298 theorems / 2,751 declarations, only propext, Classical.choice, Quot.sound.
  Actual outer-prime valuation transferred and certified. Tested merge
  db1b8b5b5cc03c70a63efbdf11d2ac0af39b2568 differs only in documentation.
- Source 1d3c2f54c765db2387b6434b87215c1ed638f494: run 40334233198 failed at
  derivative elaboration and residue-field simplification. Repaired the proof
  terms; no mathematical target was weakened.
- Source 2937b68fbe348731829a8e643a8b95c008e79fab: run 40334704332 compiled
  the Jacobian, inner fiber, all harmonic bounds, and both rational/residue
  local-block modules. Weighted-integral elaboration failed. No whole-run
  certificate inferred from these individual successes.
- Source d2f87c10add2f7f81cdf682d2e0508566b832201: run 40335293612 checks the
  weighted-integral repairs and the all-p-adic extension. Pending inspection.

No global irrationality consequence, new arithmetic rate bound, or finite-witness
closure follows merely from this local obstruction. The original manuscript-item
count remains independent of corrected-clause and component completion.
