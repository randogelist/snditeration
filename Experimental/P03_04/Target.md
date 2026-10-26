# P03_04: Root interlacing and Dodgson condensation for principal minors

Status: SOURCE_ONLY_UNCOMPILED. These experimental inputs are not proof receipts, and custom axioms must be discharged before any unconditional claim. No Lean execution was performed.

## Original statement (verbatim manuscript TeX)

```tex
\label{thm:interlacing}
Fix $K > N \ge 1$, and for $1 \le r \le h = K - N$, let $\Delta_{K, r}^{(s)}(X) := \det\big[G_K^{(s)}(X)_{i,j}\big]_{0 \le i,j < r}$ be the $r \times r$ leading principal minor polynomial.
\begin{enumerate}
\item The eigenvalues of $B_{K, r}^{(s)}$ and $B_{K, r+1}^{(s)}$ satisfy Cauchy's interlacing inequalities $\beta_1^{(r+1)} \le \beta_1^{(r)} \le \beta_2^{(r+1)} \le \dots \le \beta_r^{(r)} \le \beta_{r+1}^{(r+1)}$. Consequently, the roots of $\Delta_{K, r}^{(s)}(X)$ and $\Delta_{K, r+1}^{(s)}(X)$ interlace on $(-\infty, \zeta(s))$ and on $(\zeta(s), +\infty)$, and $\min_{1 \le j \le r} |r_j^{(r)} - \zeta(s)|$ is non-increasing in $r$.
\item For every $2 \le r \le h$ and every real root $r_j^{(r-1)}$ of $\Delta_{K, r-1}^{(s)}(X) = 0$,
\begin{equation}\label{eq:Dodgson-sign}
\Delta_{K, r}^{(s)}\!\big(r_j^{(r-1)}\big) \, \Delta_{K, r-2}^{(s)}\!\big(r_j^{(r-1)}\big) = -\Big(\Sigma_{K, r-1}^{(s)}\!\big(r_j^{(r-1)}\big)\Big)^2 \le 0,
\end{equation}
where $\Delta_{K, 0}^{(s)} := 1$ and $\Sigma_{K, r-1}^{(s)}(X)$ is the $(r-1) \times (r-1)$ minor of $G_{K, r}^{(s)}(X)$ obtained by deleting row $r-1$ and column $r-2$.
\end{enumerate}
```

## Prerequisite direction and exact scope

The literal original statement is preserved. Main's PrincipalDegreeLoss gives an actual admissible first principal polynomial with zero slope and no finite roots. Therefore the repaired candidate must retain zero eigenvalues, allow degree loss, and restrict finite reciprocal-root/minimum-distance assertions appropriately. No universal assertion of r finite roots is an assumption.

Dependency direction: actual positive principal Gram + shifted-inertia identity + already proved abstract signature restriction bounds → multiplicity-sensitive all-threshold eigenvalue interlacing. This input does not assume those inequalities. Root transport must then distinguish zero slopes from finite roots.

Part (2) takes the already imported generic polynomial symmetric block-condensation identity as support. The active exact declaration is ManuscriptChain.Dodgson.polynomial_symmetric_block_condensation, with nonzero central determinant polynomial as premise. Its actual-pencil assembly and nonzero-core proof still need to be supplied. Neither actual condensation nor its sign conclusion is assumed as an axiom.

Missing interfaces/work: compatible restriction maps and shifted signatures for two successive sizes; finite-root treatment under singular slope; actual polynomial block/deleted-minor identifications for every order. CauchyInterlacing, PrincipalRadius and PrincipalCondensation are unimported candidate discharge sources only.

Integration/discharge: prove the named actual shifted-inertia input using the pinned spectral API; preserve all real thresholds and arbitrary injective selections; compile and audit. The original finite-root wording remains repair-blocked independently of the input's eventual proof.

## Named typed inputs

- `Experimental.P03_04.actualPrincipalShiftedInertia`: The positive index of M_r−tG_r equals the number of actual whitened principal eigenvalues above t, for every real threshold t. Upstream eigenvalue-count identification; no interlacing inequality, reciprocal root comparison or Dodgson conclusion is assumed.

- `Experimental.P03_04.existingPrincipalGramInput` reuses `ManuscriptChain.Principal.principal_base_posDef`: Positive actual principal Gram for every injective index map.
