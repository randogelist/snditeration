# P03_05: Stieltjes J-fraction from interlacing roots

Status: SOURCE_ONLY_UNCOMPILED. These experimental inputs are not proof receipts, and custom axioms must be discharged before any unconditional claim. No Lean execution was performed.

## Original statement (verbatim manuscript TeX)

```tex
\label{cor:stieltjes-jfraction}
Fix $K > N \ge 1$ and $X = \zeta(s)$. Let $G := G_K^{(s)}(\zeta(s)) = L L^T$ be the lower-triangular Cholesky decomposition, and for $1 \le r \le h$, set $G_r := L_r L_r^T$ (the leading $r \times r$ principal block) and $\widehat{B}_r := L_r^{-1} M_{K, r} (L_r^{-1})^T$. Let $T_h := Q^T \widehat{B}_h Q$ be the symmetric tridiagonal reduction obtained by the Lanczos algorithm applied to $\widehat{B}_h$ with starting vector $e_h$. Write $T_h = \operatorname{tridiag}(a_1, \dots, a_h; b_1, \dots, b_{h-1})$ with $a_r \in \RR$ and $b_r > 0$. Then:
\begin{enumerate}
\item For every $X \in \RR$ with $P_K^{(s)}(X) \neq 0$, the ratio of consecutive principal-minor polynomials admits the exact finite Stieltjes continued fraction expansion
\begin{equation}\label{eq:stieltjes-jfraction}
\frac{\Delta_{K, h-1}^{(s)}(X)}{\Delta_{K, h}^{(s)}(X)} = \cfrac{1}{a_1 + (X - \zeta(s)) - \cfrac{b_1^2}{a_2 + (X - \zeta(s)) - \cfrac{b_2^2}{\ddots - \cfrac{b_{h-1}^2}{a_h + (X - \zeta(s))}}}},
\end{equation}
with strictly positive coefficients $b_1^2, \dots, b_{h-1}^2 > 0$.
\item Evaluating \eqref{eq:stieltjes-jfraction} at $X = 0$ gives the rational number $\frac{\Delta_{K, h-1}^{(s)}(0)}{\Delta_{K, h}^{(s)}(0)} \in \QQ$ (computable from the Bernoulli monomial moments $\mu_X^{(s)}(t^e)$, with no occurrence of $\zeta(s)$ in its definition), while the closest root $r_{\min} = \zeta(s) - \beta_{\max}^{-1}$ satisfies $|r_{\min} - \zeta(s)| = |\beta_{\max}|^{-1} \le e^{-K/2250}$ (Theorem~\ref{thm:root-collapse}), so the spectral edge of the J-fraction converges to $\zeta(s)$ at exponential rate.
\end{enumerate}
```

## Prerequisite direction and exact scope

Main proves an actual admissible rank-one counterexample to the literal printed formula. Preserve the original statement for comparison; do not attempt to certify it from assumptions. A corrected candidate must use resolvent I+tT, diagonal 1+t a_i, numerators t²b_i², the appropriate endpoint orientation, and the factor det(G_(h−1))/det(G_h).

The named input is an upstream finite-dimensional Lanczos existence theorem for the actual whitened matrix and a vector v. Both unit length (sum of squares =1) and full Krylov determinant nonvanishing are explicit premises. It does not assert that the manuscript's endpoint vector satisfies cyclicity, or replace an unknown no-breakdown condition by an unconditional claim. Finding/justifying the vector and handling a lower-dimensional cyclic subspace remain work.

Dependency direction: actual symmetric matrix (3.1) + explicit full-Krylov-rank vector → tridiagonal representation; representation + independent Schur-complement/continuant algebra → corrected finite resolvent fraction. Identification of the relevant principal determinant ratio must be proved separately. Part (2)'s exponential edge estimate additionally depends on actual quantitative root-collapse inputs (4.7), absent here.

Missing interfaces/work: Cholesky vs symmetric-whitened endpoint identification, correct vector orientation, finite fraction/continuant definitions, denominator nonvanishing, the Gram determinant prefactor, and evaluation at zero only when actual Delta(0)≠0. No pairwise distinctness is assumed.

Integration/discharge: replace lanczosBasisOfCyclic by a proof under precisely its displayed cyclicity premise; compile/audit all wrappers. The known false original formula is never a permitted axiom or downstream target certificate.

## Named typed inputs

- `Experimental.P03_05.lanczosBasisOfCyclic`: An explicitly unit, cyclic vector for the actual whitened manuscript matrix admits an orthogonal tridiagonalizing basis with positive adjacent entries. Only cyclic tridiagonalization. No determinant ratio, fraction identity, chosen-vector cyclicity or exponential edge bound is assumed.
