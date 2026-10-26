# P03_02: Continuous hyperbolic pencil for all real $s > 1$

Status: SOURCE_ONLY_UNCOMPILED. These experimental inputs are not proof receipts, and custom axioms must be discharged before any unconditional claim. No Lean execution was performed.

## Original statement (verbatim manuscript TeX)

```tex
\label{prop:real-s}
For any real number $s > 1$, define the positive weight $w_s(y) := \frac{(2\pi)^s}{2\Gamma(s)} y^s \sum_{l=1}^\infty l^{s-1} e^{-2\pi l y} > 0$ on $(0, \infty)$, and define the $h \times h$ real symmetric matrix pencil $G_K^{(s)}(X) := A^{(s)} + (X - \zeta(s)) M_K^{(s)}$, where
\[
A^{(s)}_{i, j} := \int_0^\infty \frac{D_N(y^2)^{2m} y^{2(i+j)}}{D_K(y^2)} w_s(y)\,dy, \qquad M_K^{(s)} := V \diag_{N < a \le K}\!\left(\frac{a^{s-1} D_N(-a^2)^{2m-1}}{D_{\mathrm{tail}}'(-a^2)}\right) V^T.
\]
Then for every real $s > 1$, $G_K^{(s)}(X)$ coincides at odd integers $s = 2k+1$ with \eqref{eq:GK-def}, and $\Delta_K^{(s)}(X) := \det G_K^{(s)}(X)$ is a polynomial of exact degree $h$ with all $h$ roots real.
```

## Prerequisite direction and exact scope

This branch preserves original Proposition 3.2 literally. Its odd-weight coincidence is false with the printed prefactor: the printed density is π/2 times the odd-weight density. The separate corrected candidate uses 2(2π)^(s−1)/Γ(s). Main already proves the corrected candidate; this branch supplies only named interfaces to its two independently proved upstream facts and does not relabel the printed proposition as proved.

Dependency direction: positive real-weight Gram plus nonsingular real symmetric slope → corrected spectral degree/real-root theorem by the established Theorem 3.1 machinery. Both inputs are actual matrices, not abstract Prop placeholders. No new axiom is appropriate or needed.

Covered formulas: actual corrected Gram positivity and nonzero direction determinant. These aliases do not assert the target proposition or literal odd-weight coincidence. The existing active declarations ContinuousWeight.proposition_3_2_corrected and pencil_odd remain the distinct corrected endpoint. The unimported ContinuousParameter source is not used.

Integration/discharge: compile and audit these wrappers at the destination pin; verify imported dependencies match main; keep the literal/corrected normalization distinction. No mathematical premise is pending in these aliases; editorial correction of the original formula is necessary before original-statement closure could be recorded.

## Named typed inputs

No new axioms: the required upstream facts are already proved and are exposed as typed aliases.

- `Experimental.P03_02.correctedGramInput` reuses `ManuscriptChain.ContinuousWeight.gram_posDef`: Positive definiteness of the actual corrected continuous-weight Gram matrix for s>0.
- `Experimental.P03_02.correctedSlopeInput` reuses `ManuscriptChain.ContinuousWeight.direction_det_ne_zero`: Nonsingular actual continuous slope.
