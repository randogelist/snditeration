# Next open original theorem — 3.3

The repair campaign on [PR #39](https://github.com/randogelist/snditeration/pull/39)
has verified the earlier arbitrary-L² Beukers–Krein endpoint, including actual
kernel square-integrability, the convergent signed-mode identity and independence
of the chosen almost-everywhere representative. Both parts (1) and (2) of 5.2
are complete on that branch; the fixed-K cone clause in part (3) needs correction.
The branch is not merged into main. See the immutable
[completion receipt](receipts/COMPLETION_20261026.json) and
[correction log](FORMALIZATION_CORRECTIONS.md).

The next open original is **Theorem 3.3(1)**. The branch now proves an explicit
factorial majorant for every actual moment, actual Carleman divergence,
translated sparse and solid minors of all orders, arbitrary mixed 2×2 minors,
finite mass, and exact square-root coordinate identities. None of these alone
proves the two remaining assertions:

1. **Arbitrary mixed-minor strict positivity in all orders.** Prove generalized
   Vandermonde positivity for strictly increasing natural exponents and positive
   nodes; establish the corresponding Andréief integration identity with every
   integrability premise justified; then prove strict positivity for the actual
   measure. The existing sparse/translated and size-two results must not be
   substituted for arbitrary unrelated row and column exponent selections.
2. **Stieltjes measure uniqueness.** Transfer the actual factorial bound to any
   competing positive-half-line measure with the same moments. One concrete
   route is exponential square-root integrability, symmetric square-root
   pushforward, analytic moment-generating-function equality, characteristic
   function uniqueness and pushback by squaring. The new coordinate identities
   are prerequisites; the exponential-integrability and uniqueness bridges
   still need proofs. Alternatively formalize a complete Stieltjes Carleman
   theorem and instantiate all of its hypotheses from the actual source.

Use the same Lean 4.33.0 and pinned Mathlib state as the receipt. A completed
endpoint requires successful permitted-target compilation, complete transitive
axiom evidence, and verified membership in the built import graph. Experimental
prerequisite declarations and their publication receipts remain unchanged until
an explicit branch update consumes the proved library inputs.

Other independent open work is listed item by item in
[FORMALIZATION_STATUS.json](FORMALIZATION_STATUS.json). In particular, the
corrected resolvent fraction in 3.5, individual centered-coefficient nonvanishing
in 3.7, and actual quantitative arithmetic estimates in Chapters 4–6 remain
separate obligations. No corrected theorem proves a false original.

The historical finite-Krein receipt remains [CI 40271072845](https://github.com/randogelist/snditeration/actions/runs/40271072845)
at source `372deda8edc77bba6312b8f80137e00e1b75e74f`; it is preserved as an earlier
monomial/finite-coefficient checkpoint, not the final arbitrary-L² evidence.
