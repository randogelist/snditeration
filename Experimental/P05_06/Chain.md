# Proposed chain — manuscript 5.6

Role: PROP. Stage: construction. Status: SOURCE_ONLY_UNCOMPILED.

This branch preserves the exact original target, typed prerequisites, repair gates and immutable publication receipt from [d41b2d7600892844fa5dde219531439fa86e8258](https://github.com/randogelist/snditeration/tree/d41b2d7600892844fa5dde219531439fa86e8258). No inherited proof status is upgraded by this branch label.

- [Original target and repair boundary](Target.md)
- [Named assumptions](Assumptions.json)
- [Alternative chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p05-06_alt_construction)

## Input contract

Reuse the proved prerequisites identified in Assumptions.json. Undischarged custom axioms remain explicit research inputs. Never assume the target itself, a known-false predecessor, or a circular family of targets. A corrected predecessor from an ALT branch is admissible only after its exact output is proved to imply this target's required input; a weaker result is not an automatic substitute.

The existing experimental Lean files and source-only publication receipt are unchanged. Their namespaces do not constitute a logical sandbox: no certified root may import these modules while their research axioms remain dependencies.

## Acceptance

Keep the original and alternative theorem statuses separate. The alternative does not certify this original. Require exact-source compiler and transitive axiom evidence before any new !!; custom-axiom-dependent results stay explicitly conditional. No Lean execution, proof-source changes or builds are part of this branch publication.
