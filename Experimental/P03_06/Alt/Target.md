# Alternative chain — manuscript 3.6

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-06_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/9b56739b36897fbd1564f6cdaea57219320d9e57/Experimental/P03_06/Target.md)

## Selected alternative target

For an actual real-rooted polynomial P of degree h≥1, with its h roots listed with multiplicity, and real q0 with P(q0)≠0, set u_j=(r_j−q0)^−2 and S_2r=∑u_j^r. Target positive semidefinite Hankel matrices, strict positivity only up to the number of distinct u_j, vanishing determinants above that rank, and h^(−1/(2r))d_min≤S_2r^(−1/(2r))≤d_min for r≥1.

Relation to original: **corrected**.

Replace impossible all-order strict Hankel positivity and reverse the printed finite-rate inequality to its correct direction; audit the logarithmic-derivative sign separately.

## Candidate upstream inputs

3.1. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Finite Gram rank/distinct-support argument and nearest-distance limit.
- Exact rational power-sum/logarithmic-derivative identification using log|P| on a root-free neighborhood.

Correction gate: Multiplicity of roots and coincident reciprocal-square nodes must be counted separately.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P03_06/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/9b56739b36897fbd1564f6cdaea57219320d9e57/Experimental/P03_06/Prerequisites.lean)
- [Experimental/P03_06/Target.md](https://github.com/randogelist/snditeration/blob/9b56739b36897fbd1564f6cdaea57219320d9e57/Experimental/P03_06/Target.md)
