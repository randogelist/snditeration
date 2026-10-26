# Alternative chain — manuscript 3.9

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-09_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/b361758244315c7a9a3b5d5ef555122cdddf3bf3/Experimental/P03_09/Target.md)

## Selected alternative target

Restrict the character part initially to the five explicit coefficient tables χ−3, χ−4, χ5, χ8 and χ−8, proving their geometric generating identities and positivity; build their actual moment pencils with explicit centers. Treat the shifted Hurwitz pole-integral realization as a separate conditional subtarget.

Relation to original: **restricted**.

Replace automatic coverage of all named Mathlib characters by five concrete tables until character identification/exhaustion is proved; do not assume the unverified shifted scalar identity without independent verification.

## Candidate upstream inputs

2.5, 3.1. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- All-order moment integrability and pole domains.
- L-value/parity and Hurwitz-series identifications.
- Exact shifted pole-integral remainder and arithmetic rationality.

Correction gate: Positive kernels alone do not certify the rational Hurwitz functional or correct zeta/L center.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P03_09/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/b361758244315c7a9a3b5d5ef555122cdddf3bf3/Experimental/P03_09/Prerequisites.lean)
- [Experimental/P03_09/Target.md](https://github.com/randogelist/snditeration/blob/b361758244315c7a9a3b5d5ef555122cdddf3bf3/Experimental/P03_09/Target.md)
