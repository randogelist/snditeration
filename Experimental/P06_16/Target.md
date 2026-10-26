# Theorem 6.16: Generalized multi-weight Zeta--Beta positive-definite pencil

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:multiweight_zeta_beta_1var}
Fix an integer $k\ge 1$ and integer tuples $\mathbf{b}=(b_{1},\dots,b_{k})\in\mathbb{Z}^{k}$ ($b_{k}>0$) and $\mathbf{a}=(a_{1},\dots,a_{k})\in\mathbb{Z}^{k}$. For $K>N\ge 1$ ($h=K-N$), $M\ge 1$, and $R_{i,j}(t)=\frac{D_{N}(t)^{2M}t^{i+j}}{D_{K}(t)}$ ($0\le i,j<h$), define the $h\times h$ Hankel matrix
\[
G_{K}^{[\mathbf{b},\mathbf{a}]}(Z):=\left[\sum_{m=1}^{k}b_{m}\mu_{X_{m}}^{(2m+1)}\!\big((-t)^{k-m}R_{i,j}(t)\big)+\sum_{r=1}^{k}\frac{a_{r}}{4^{r-1}}\widetilde{\mu}_{Y_{r}}^{(\beta(2r))}\!\big((-t)^{k+1-r}R_{i,j}(t)\big)\right]_{0\le i,j<h},
\]
where $Z:=\sum_{m=1}^{k}b_{m}X_{m}+\sum_{r=1}^{k}a_{r}Y_{r}$, and set $\xi_{\mathbf{b},\mathbf{a}}:=\sum_{m=1}^{k}b_{m}\zeta(2m+1)+\sum_{r=1}^{k}a_{r}\beta(2r)$. Then:
\begin{enumerate}
\item[(1)] \textup{(Exact integral representation and $Z$-derivative)} The matrix $G_{K}^{[\mathbf{b},\mathbf{a}]}(Z)$ is affine linear in the single indeterminate $Z$ with $Z$-derivative $[Z]G_{K}^{[\mathbf{b},\mathbf{a}]}(Z)=M_{K}^{(2k+1)}$ identical to the pure weight-$(2k+1)$ Riemann zeta derivative matrix. At $X_{m}=\zeta(2m+1)$ and $Y_{r}=\beta(2r)$ ($Z=\xi_{\mathbf{b},\mathbf{a}}$),
\[
G_{K}^{[\mathbf{b},\mathbf{a}]}(\xi_{\mathbf{b},\mathbf{a}})_{i,j}=\int_{0}^{\infty}\frac{D_{N}(v^{2})^{2M}v^{2(i+j)}}{D_{K}(v^{2})}W_{\mathbf{b},\mathbf{a}}(v)\,dv,
\]
where the combined Zeta--Beta weight on $(0,\infty)$ is
\[
W_{\mathbf{b},\mathbf{a}}(v):=\sum_{m=1}^{k}(-1)^{k-m}b_{m}v^{2k-2m}w_{2m+1}(v)+\sum_{r=1}^{k}\frac{(-1)^{k+1-r}a_{r}}{4^{r-1}}v^{2k+2-2r}\widetilde{w}_{\beta(2r)}(v).
\]
\item[(2)] \textup{(Universal hyperbolicity, bilateral signature, and zero-free disk on the positivity cone)} For every pair of tuples $(\mathbf{b},\mathbf{a})\in\mathbb{Z}^{k}\times\mathbb{Z}^{k}$ such that $W_{\mathbf{b},\mathbf{a}}(v)>0$ for all $v>0$ and $\lim_{v\to\infty}W_{\mathbf{b},\mathbf{a}}(v)/w_{2k+1}(v)>0$, there exist constants $0<c_{1}(\mathbf{b},\mathbf{a})\le c_{2}(\mathbf{b},\mathbf{a})<\infty$ such that $c_{1}(\mathbf{b},\mathbf{a})w_{2k+1}(v)\le W_{\mathbf{b},\mathbf{a}}(v)\le c_{2}(\mathbf{b},\mathbf{a})w_{2k+1}(v)$ for all $v>0$. Consequently, $G_{K}^{[\mathbf{b},\mathbf{a}]}(\xi_{\mathbf{b},\mathbf{a}})\succ 0$ is strictly positive definite, all $h$ roots of $\det G_{K}^{[\mathbf{b},\mathbf{a}]}(Z)=0$ are real, split with signature $(\lfloor h/2\rfloor,\lceil h/2\rceil)$ across $\xi_{\mathbf{b},\mathbf{a}}$, and satisfy $|r_{j}-\xi_{\mathbf{b},\mathbf{a}}|\ge c_{1}(\mathbf{b},\mathbf{a})\|B_{K}^{(2k+1)}\|^{-1}$.
\item[(3)] \textup{(Zero odd-prime denominator overhead)} At every odd prime $p>\max(\|\mathbf{b}\|_{\infty},\|\mathbf{a}\|_{\infty},2k+3)$, all monomial moments of $\widetilde{\mu}_{Y_{r}}^{(\beta(2r))}$ are $p$-adically integral ($v_{p}\ge 0$) because $E_{2e}\in\mathbb{Z}$, and all harmonic sums $H_{2j}^{(\beta,2r)}$ have $p$-adic valuation $\ge -2r>-(2k+1)$, so adding $\sum_{r=1}^{k}a_{r}\beta(2r)$ incurs zero odd-prime denominator penalty in the quadratic exponent $A_{M}^{(2k+1)}$.
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 2.2, 2.5, 3.1, 3.3, 6.6, 6.14. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.Hyperbolic.density_pos`
- `ManuscriptChain.Real.derivativeMatrix`

## Typed prerequisite coverage

Actual integer tuple data, genuine zeta/beta values, finite beta harmonic sums and the common-pole algebraic coefficient. Existing pure-zeta density and derivative APIs are imported. No unverified scaled functional is silently postulated.

## Explicit assumptions

No new axioms. The useful current interface consists of concrete data and imported results; missing analytic/arithmetic infrastructure is left open.

## Missing domain interfaces

The repaired 6.14 beta functional; exact affine collapse; analytic combined-weight definition and endpoint estimates; uniform comparison; correct signature parity and all prime valuations.

## Repair and discharge gates

- Blocked on the normalization repair in 6.14; no printed conflicting pole/integral identities are axioms.
- Check both boundary ratios and parity hypotheses before importing uniform comparison and signature.
- Odd-prime integrality does not settle the dyadic multiplier.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
