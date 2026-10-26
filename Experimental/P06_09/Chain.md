# Proposed chain — manuscript 6.9

Role: PROP. Stage: construction. Status: SOURCE_ONLY_UNCOMPILED.

This branch preserves the exact original target, typed prerequisites, repair gates and immutable publication receipt from [c88ecbb039e08e8355065b5e9649183e1f934e2e](https://github.com/randogelist/snditeration/tree/c88ecbb039e08e8355065b5e9649183e1f934e2e). No inherited proof status is upgraded by this branch label.

- [Original target and repair boundary](Target.md)
- [Named assumptions](Assumptions.json)
- [Alternative chain](https://github.com/randogelist/snditeration/tree/experiment/zetahyperbolic-p06-09_alt_construction)

## Input contract

Reuse the proved prerequisites identified in Assumptions.json. Undischarged custom axioms remain explicit research inputs. Never assume the target itself, a known-false predecessor, or a circular family of targets. A corrected predecessor from an ALT branch is admissible only after its exact output is proved to imply this target's required input; a weaker result is not an automatic substitute.

The existing experimental Lean files and source-only publication receipt are unchanged. Their namespaces do not constitute a logical sandbox: no certified root may import these modules while their research axioms remain dependencies.

## Acceptance

Keep the original and alternative theorem statuses separate. The alternative does not certify this original. Require exact-source compiler and transitive axiom evidence before any new !!; custom-axiom-dependent results stay explicitly conditional. No Lean execution, proof-source changes or builds are part of this branch publication.
