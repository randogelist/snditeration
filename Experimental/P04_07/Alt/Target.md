# Alternative chain — manuscript 4.7

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p04-07_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/24ead265dee4b6732386e42336df3ec4dc49426a/Experimental/P04_07/Target.md)

## Selected alternative target

Prove a conditional finite cap-and-average root-clustering theorem on the actual family: an explicit spectral cap on the actual whitened slope B and a normalized lower bound for log|det B| (with det B≠0) imply a multiplicity-counted cluster count. Add root separation only under actual polynomial height/leading-coefficient and squarefree-factor data; keep nearest-root decay dependent on a separate small nonzero center evaluation.

Relation to original: **conditional**.

Separate clustering, nearest-root decay and arithmetic separation; retain error constants and onsets rather than treating asymptotic notation as effective data.

## Candidate upstream inputs

3.1, 4.4, 4.6. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Identify the exact lower bound for log|det B| of the actual whitened slope B; a lower bound for the Gram determinant alone is not this premise.
- Cap-and-average inequality and reciprocal spectral/root transport.
- Actual polynomial factor heights and discriminant separation.
- Small center evaluation and quantified O(K log K) error budget.

Correction gate: A replacement 4.4_alt or 4.6_alt supplies this branch only after an explicit bridge proves the precise input clause used here.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Experimental/P04_07/Prerequisites.lean](https://github.com/randogelist/snditeration/blob/24ead265dee4b6732386e42336df3ec4dc49426a/Experimental/P04_07/Prerequisites.lean)
- [Experimental/P04_07/Target.md](https://github.com/randogelist/snditeration/blob/24ead265dee4b6732386e42336df3ec4dc49426a/Experimental/P04_07/Target.md)
