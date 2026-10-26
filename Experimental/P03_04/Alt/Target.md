# Alternative chain — manuscript 3.4

Role: ALT. Stage: construction. Status: DOCUMENTATION_ONLY_CANDIDATE.

[Original proposed chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p03-04_prop_construction) · [Verbatim original and repair gates](https://github.com/randogelist/snditeration/blob/06efc463a549f07db26b8e38f565276e8854d476/Experimental/P03_04/Target.md)

## Selected alternative target

For the actual nested principal pencils, prove interlacing first for the generalized symmetric eigenvalues, allowing zero eigenvalues; transport only nonzero eigenvalues to finite roots with multiplicities and sign-aware reciprocal ordering. State the actual Dodgson identity separately, retaining any nonzero-central-minor premise.

Relation to original: **corrected**.

Allow principal degree loss and roots at infinity instead of asserting r finite roots at every size.

## Candidate upstream inputs

3.1. These are clause-selection tasks, not new axioms or certified dependency edges.

## Remaining obligations

- Actual shifted-inertia identification and nested compression/interlacing proof.
- Actual pencil substitution in the generic Dodgson identity.

Correction gate: The known constant principal-pencil case must satisfy the corrected statement; a full-root-count predecessor cannot be assumed.

## Dual-chain input and acceptance rules

PROP preserves the original manuscript target. ALT records a separately named corrected, restricted, conditional or alternate-route target; it is not a proof of the original and is not presumed to repair every downstream claim.

Prerequisite item numbers below are candidate input locations, not blanket assumptions of entire printed theorems. For each one, select the exact source clause and track its hypotheses, definitions and evidence. If that input has a correction, use only the compatible corrected clause. A downstream consumer must prove that the selected ALT output supplies its exact required input, or explicitly revise its own target. Weaker statements do not automatically replace stronger ones. No cycle, known-false predecessor or own-target axiom is admissible proof progress.

This ALT branch is based on the main source snapshot and adds documentation only. It does not import or copy the PROP experiment's prerequisite axioms. No ALT Prerequisites.lean, Work.lean, target declaration or compiler receipt is created by this step. Constructing those typed interfaces remains work to do. The main snapshot's historical proofs keep their own immutable evidence; candidate and unimported files receive no new certification.

Before integration: fix the exact formal target and input clauses, prove any compatibility bridge, discharge custom axioms or expose them as explicit conditional hypotheses, then inspect the complete relevant compiler and transitive axiom evidence on the authorized target. No local Lean, workflow dispatch, proof-tier promotion or new theorem certification occurs in this publication.

## Immutable source locations

- [Zetahyperbolic/Section3/PrincipalDegreeLoss.lean](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/Zetahyperbolic/Section3/PrincipalDegreeLoss.lean)
- [Zetahyperbolic/Section3/SignatureRestriction.lean](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/Zetahyperbolic/Section3/SignatureRestriction.lean)
- [Zetahyperbolic/Section3/DodgsonCondensation.lean](https://github.com/randogelist/snditeration/blob/a3904c2a97b47b0dc2af41dcc708ca41c968da96/Zetahyperbolic/Section3/DodgsonCondensation.lean)
