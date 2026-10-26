# P03_06: Stieltjes reciprocal-root power sums

Status: SOURCE_ONLY_UNCOMPILED. These experimental inputs are not proof receipts, and custom axioms must be discharged before any unconditional claim. No Lean execution was performed.

## Original statement (verbatim manuscript TeX)

```tex
\label{cor:stieltjes-hierarchy}
For any fixed $K$ and any rational shift $q_0 \in \QQ$ with $P_K^{(s)}(q_0) \neq 0$, define the rational power sums
\[
S_m(q_0) := \frac{(-1)^{m-1}}{(m-1)!} \left.\frac{d^m}{dX^m} \log P_K^{(s)}(X)\right|_{X = q_0} = \sum_{j=1}^h \frac{1}{(r_{K, j} - q_0)^m} \in \QQ \qquad (m \ge 1).
\]
Then $\{S_{2r}(q_0)\}_{r \ge 0}$ ($S_0(q_0) := h$) is a positive Stieltjes moment sequence with strictly positive Hankel determinants, and at each fixed $K$ the inner limit $\lim_{r \to \infty} \big(S_{2r}(q_0)\big)^{-1/(2r)} = d_{\min}(K) := \min_{1 \le j \le h} |r_{K, j} - q_0|$ converges with factor $1 \le \big(S_{2r}(q_0)\big)^{-1/(2r)} / d_{\min}(K) \le h^{1/(2r)}$ for all $r \ge 1$.
```

## Prerequisite direction and exact scope

The literal original corollary is false: a finite-support measure cannot have strictly positive Hankel determinants at all orders; main contains an actual reciprocal-square rank-one counterexample. The printed estimator inequalities are reversed, and the odd-order logarithmic derivative convention has a sign mismatch. Preserve those original formulas below, but use a separate corrected candidate.

The named input is a finite sum-of-squares expansion, independent of any positivity conclusion. Its nodes are exactly reciprocals of squared distances from the actual spectral roots to rational q. The identity itself is algebraic and remains valid under totalized division; applying it to the target requires the original nonvanishing P(q)≠0 and the actual root characterization, so that each reciprocal node is positive. No such root-avoidance or node-distinctness conclusion is silently assumed.

Dependency direction: actual root factorization (3.1) + q not a root → positive finite reciprocal-square nodes; Gram expansion → PSD Hankel forms. Exact determinant positivity requires order bounded by the number of distinct nodes plus Vandermonde-rank arguments. Above that rank determinants vanish. Repeated squared distances must be grouped before a strictness statement.

Existing ACTUAL_RECIPROCAL_MOMENT_BOUNDS and ACTUAL_RECIPROCAL_MOMENT_LIMIT cover the corrected estimator at the actual spectral center; they are not an arbitrary-rational-shift logarithmic-derivative theorem. Missing interfaces/work: polynomial-to-log derivative identities with correct sign, rationality of all power sums at rational nonroots, shift-specific minimum-distance selection, grouped finite support and exact rank, and general-q estimator bounds/limit.

Integration/discharge: the single named axiom is intended to be replaced by finite sum/power algebra, then audited. Continue on the explicitly corrected finite-support corollary; never assume or conclude all-order strict Hankel positivity.

## Named typed inputs

- `Experimental.P03_06.actualFiniteMomentGramExpansion`: Quadratic form of the actual finite reciprocal-square moment Hankel matrix equals a finite sum of polynomial squares at its actual spectral nodes. Upstream exact finite algebra for positive-semidefiniteness; not the target strict positivity/rank/logarithmic derivative/limit assertions.
