# Theorem 6.17: Universal two-variable Beukers Zeta--Beta pencil, Krein decomposition, and $q$-adic non-vanishing

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:two_var_zeta_beta}
Fix any integer $k\ge 1$ and any non-zero pair of integer tuples $(\mathbf{b},\mathbf{a})\in(\mathbb{Z}^{k}\times\mathbb{Z}^{k})\setminus\{(\mathbf{0},\mathbf{0})\}$. Define the coupled two-variable signed measure on $(0,1)^{2}$ by
\[
d\Omega_{\mathbf{b},\mathbf{a}}^{(\zeta,\beta)}(x_{1},x_{2}):=\sum_{m=1}^{k}b_{m}\frac{16(x_{1}x_{2})^{3}\big(-4\log(x_{1}x_{2})\big)^{2m-1}}{(2m)!\big(1-x_{1}^{4}x_{2}^{4}\big)}\,dx_{1}\,dx_{2}+\sum_{r=1}^{k}a_{r}\frac{\big(-\log(x_{1}x_{2})\big)^{2r-2}}{(2r-1)!\big(1+x_{1}^{2}x_{2}^{2}\big)}\,dx_{1}\,dx_{2}.
\]
For any $h$-dimensional polynomial subspace $\mathcal{A}=\{A_{0}(x^{4}),\dots,A_{h-1}(x^{4})\}\subset\mathbb{Q}[x^{4}]_{\le 4K}$ with coefficient matrix $C\in M_{h\times(K+1)}(\mathbb{Q})$, define the $h\times h$ symmetric matrix pencil $G_{\mathcal{A}}^{[\mathbf{b},\mathbf{a}]}(Z)$ in $Z:=\sum_{m=1}^{k}b_{m}X_{m}+\sum_{r=1}^{k}a_{r}Y_{r}$ by
\[
G_{\mathcal{A}}^{[\mathbf{b},\mathbf{a}]}(Z)_{i,j}:=\sum_{n=0}^{K}C_{i,n}C_{j,n}\left(Z-\sum_{m=1}^{k}b_{m}H_{n}^{(2m+1)}-\sum_{r=1}^{k}a_{r}H_{2n}^{(\beta,2r)}\right)+\sum_{0\le n\neq l\le K}C_{i,n}C_{j,l}\frac{\Delta H_{n,l}^{[\mathbf{b},\mathbf{a}]}}{n-l},
\]
where $\Delta H_{n,l}^{[\mathbf{b},\mathbf{a}]}:=\sum_{m=1}^{k}\frac{b_{m}}{2m}\big(H_{n}^{(2m)}-H_{l}^{(2m)}\big)+\sum_{r=1}^{k}\frac{a_{r}}{4(2r-1)}\big(H_{2n}^{(\beta,2r-1)}-H_{2l}^{(\beta,2r-1)}\big)$. Set $\xi_{\mathbf{b},\mathbf{a}}:=\sum_{m=1}^{k}b_{m}\zeta(2m+1)+\sum_{r=1}^{k}a_{r}\beta(2r)$ and $\Delta_{\mathcal{A}}^{[\mathbf{b},\mathbf{a}]}(Z):=\det G_{\mathcal{A}}^{[\mathbf{b},\mathbf{a}]}(Z)\in\mathbb{Q}[Z]$. Then:
\begin{enumerate}
\item[(1)] \textup{(Universal hyperbolicity and zero quadratic derivative growth)} For every $(\mathbf{b},\mathbf{a})\neq(\mathbf{0},\mathbf{0})$, $[Z]G_{\mathcal{A}}^{[\mathbf{b},\mathbf{a}]}(Z)=CC^{T}\succ 0$ is strictly positive definite, all $h$ roots of $\Delta_{\mathcal{A}}^{[\mathbf{b},\mathbf{a}]}(Z)$ are unconditionally real, and for polynomially bounded integer matrices $C_{K}\in M_{h\times(K+1)}(\mathbb{Z})$, $\lim_{K\to\infty}K^{-2}\log\det([Z]G_{\mathcal{A}_{K}}^{[\mathbf{b},\mathbf{a}]}(Z))=0$.
\item[(2)] \textup{(Krein-space decomposition and positive/negative subspaces $\mathcal{A}_{\pm}$)} At $Z=\xi_{\mathbf{b},\mathbf{a}}$, the bilinear form $\iint_{(0,1)^{2}}f(x_{1}^{4})f(x_{2}^{4})\,d\Omega_{\mathbf{b},\mathbf{a}}^{(\zeta,\beta)}(x_{1},x_{2})$ decomposes into an infinite-rank Krein difference of squares, yielding explicit $h$-dimensional subspaces $\mathcal{A}_{+},\mathcal{A}_{-}\subset\mathbb{Q}[x^{4}]_{\le 4K}$ such that $G_{\mathcal{A}_{+}}^{[\mathbf{b},\mathbf{a}]}(\xi_{\mathbf{b},\mathbf{a}})\succ 0$ (all roots $r_{j}<\xi_{\mathbf{b},\mathbf{a}}$) and $G_{\mathcal{A}_{-}}^{[\mathbf{b},\mathbf{a}]}(\xi_{\mathbf{b},\mathbf{a}})\prec 0$ (all roots $r_{j}>\xi_{\mathbf{b},\mathbf{a}}$).
\item[(3)] \textup{(Unconditional $q$-adic non-vanishing for arbitrary Zeta--Beta linear forms)} Suppose $\sum_{m=1}^{k}b_{m}\zeta(2m+1)+\sum_{r=1}^{k}a_{r}\beta(2r)=c\in\mathbb{Z}$, and let $s_{*}:=\max\big(\{2m+1:b_{m}\neq 0\}\cup\{2r:a_{r}\neq 0\}\big)\ge 2$ be the highest active weight in $(\mathbf{b},\mathbf{a})$. Then for every prime $q>\max(\|\mathbf{b}\|_{\infty},\|\mathbf{a}\|_{\infty},s_{*}+5)$:
\begin{enumerate}
\item[(i)] If $s_{*}=2m_{*}+1$ is odd ($b_{m_{*}}\neq 0$), setting $K=2q-1$, $h=q$, and $\mathcal{A}_{q}:=\{x^{4\rho}+\kappa_{m_{*}}x^{4(\rho+q)}:0\le\rho<q\}$ ($\kappa_{m_{*}}=1$ for $m_{*}\ge 2$ and $\kappa_{1}=2$) gives the exact $q$-adic valuation
\[
v_{q}\!\left(\Delta_{\mathcal{A}_{q}}^{[\mathbf{b},\mathbf{a}]}(c)\right)=-(2m_{*}+1)q<0\quad\Longrightarrow\quad\Delta_{\mathcal{A}_{q}}^{[\mathbf{b},\mathbf{a}]}(c)\neq 0.
\]
\item[(ii)] If $s_{*}=2r_{*}$ is even ($a_{r_{*}}\neq 0$), setting $K=q-1$, $h=(q-1)/2$, and $\mathcal{A}_{q}^{(\beta)}:=\{x^{4\rho}+2x^{4(\rho+(q+1)/2)}:0\le\rho<(q-1)/2\}$ gives the exact $q$-adic valuation
\[
v_{q}\!\left(\Delta_{\mathcal{A}_{q}^{(\beta)}}^{[\mathbf{b},\mathbf{a}]}(c)\right)=-2r_{*}\!\left(\frac{q-1}{2}\right)=-r_{*}(q-1)<0\quad\Longrightarrow\quad\Delta_{\mathcal{A}_{q}^{(\beta)}}^{[\mathbf{b},\mathbf{a}]}(c)\neq 0.
\]
\end{enumerate}
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 5.2, 5.3, 6.7, 6.10. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.DualSpectral.coefficientSlope_posDef`
- `ManuscriptChain.Beukers.polynomialMomentForm_eq_krein`
- `ManuscriptChain.CoefficientGramGrowth.normalized_log_det_tendsto_zero`

## Typed prerequisite coverage

Actual beta-four integral base case as separately named prior-item assumptions, plus existing genuine zeta-seven moments/Krein bilinear identity, coefficient-Gram positivity and growth facts.

## Explicit assumptions

- `Experimental.P06_17.upstream_beta_four_diagonal_moment`: Concrete diagonal integral identity from earlier Proposition 5.3, only beta weight four; no arbitrary-weight or q-adic conclusion is assumed.
- `Experimental.P06_17.upstream_beta_four_offdiagonal_moment`: Concrete rational off-diagonal integral identity from earlier Proposition 5.3, only beta weight four.

## Missing domain interfaces

Higher even-beta moments, multiweight assembly, all required signed-channel and positive/negative-subspace arguments, exact local matrices and corrected q-adic leading terms.

## Repair and discharge gates

- The q=11 odd-harmonic denominator and q=41 leading-diagonal counterchecks refute printed proof steps. Do not assume those local congruences.
- Recompute the actual 2j+1 denominator ranges for every selected basis before using a valuation formula.
- Krein decomposition does not by itself construct uniformly definite finite-dimensional subspaces.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
