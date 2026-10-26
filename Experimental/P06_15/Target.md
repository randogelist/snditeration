# Theorem 6.15: Arithmetic transcendence, strictly positive one-variable measure, and rank-one Padé pencil for $\beta(2k+1)$ across all $k\ge 0$

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:beta_odd_weights}
For every integer $k\ge 0$, let $\beta(2k+1)=\sum_{n=0}^{\infty}(-1)^{n}(2n+1)^{-(2k+1)}=\frac{(-1)^{k}E_{2k}}{2(2k)!}\big(\frac{\pi}{2}\big)^{2k+1}$. Then:
\begin{enumerate}
\item[(1)] \textup{(Unconditional transcendence, $\overline{\mathbb{Q}}$-linear independence, and effective irrationality measure)} For every $k\ge 0$, $\beta(2k+1)$ is transcendental over $\mathbb{Q}$, and for any $N\ge 1$ the set $\{1,\beta(1),\beta(3),\dots,\beta(2N+1)\}$ is linearly independent over $\overline{\mathbb{Q}}$. Moreover, for every $k\ge 0$ there exists an effectively computable constant $C_{k}>0$ such that $|\beta(2k+1)-a/b|>b^{-C_{k}}$ for all $a,b\in\mathbb{Z}$ with $b\ge 2$ (with $|\beta(1)-a/b|>b^{-7.10321}$ for all large $b$ at $k=0$).
\item[(2)] \textup{(Strictly positive one-variable measure and totally positive Hankel pencil for all $\beta(2k+1)$)} Define the strictly positive measure on $u\in(0,1)$ by
\[
d\nu_{2k+1}(u):=\frac{1}{(2k)!}\frac{(-\log u)^{2k}}{1+u^{2}}\,du>0\qquad (u\in(0,1)).
\]
Then for every integer $r\ge 0$, its moments are given by
\[
\int_{0}^{1}u^{2r}\,d\nu_{2k+1}(u)=(-1)^{r}\big(\beta(2k+1)-H_{r}^{(\beta,2k+1)}\big),\qquad \int_{0}^{1}u^{2r+1}\,d\nu_{2k+1}(u)=\frac{(-1)^{r}}{2^{2k+1}}\big(\eta(2k+1)-H_{r}^{(\eta,2k+1)}\big),
\]
where $\eta(s)=(1-2^{1-s})\zeta(s)$ and $H_{r}^{(\eta,s)}:=\sum_{n=1}^{r}(-1)^{n-1}n^{-s}$. Consequently, for any integers $K>N\ge 0$ ($h=K-N$), defining the $h\times h$ Hankel matrix pencil $G_{K}^{(\beta(2k+1))}(X):=\big[(-1)^{N+i+j}(X-H_{N+i+j}^{(\beta,2k+1)})\big]_{0\le i,j<h}\in M_{h}(\mathbb{Q}[X])$:
\begin{enumerate}
\item[(i)] At $X=\beta(2k+1)$, $G_{K}^{(\beta(2k+1))}(\beta(2k+1))=\big[\int_{0}^{1}u^{2(N+i+j)}\,d\nu_{2k+1}(u)\big]_{0\le i,j<h}\succ 0$ is strictly totally positive of all orders for every $k\ge 0$.
\item[(ii)] The $X$-derivative matrix $M_{K}^{(\beta(2k+1))}:=[X]G_{K}^{(\beta(2k+1))}(X)=(-1)^{N}v_{-}v_{-}^{T}$ ($v_{-}:=(1,-1,1,\dots,(-1)^{h-1})^{T}$) has rank $1$, so $\Delta_{K}^{(\beta(2k+1))}(X):=\det G_{K}^{(\beta(2k+1))}(X)$ is an exact degree-$1$ linear form in $X$ whose unique root $r_{K}\in\mathbb{Q}$ satisfies $(-1)^{N}(\beta(2k+1)-r_{K})>0$ and converges to $\beta(2k+1)$ at the geometric rate
\[
\big|\beta(2k+1)-r_{K}\big|=\Big(v_{-}^{T}G_{K}^{(\beta(2k+1))}(\beta(2k+1))^{-1}v_{-}\Big)^{-1}\asymp_{k,N} h^{-2k}\big(3+2\sqrt{2}\big)^{-2h}\qquad (h\to\infty).
\]
\end{enumerate}
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 3.8, 5.1. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.UnitLogMoments.integral_pow_log`
- `ManuscriptChain.UnitLogMoments.integrable_pow_log`

## Typed prerequisite coverage

Actual beta-one integral ∫_(0,1) (1+u²)^(-1) du; for s≥2 the absolutely convergent alternating beta series; rational harmonic tails, the odd-beta density formula, eta(1) removable value and existing exact Mellin logarithmic moments. Independent pi nonvanishing and geometric expansion are explicit assumptions. No pi/4 value is included in the beta-one definition.

## Explicit assumptions

- `Experimental.P06_15.upstream_pi_polynomial_nonvanishing`: Nonvanishing of every nonzero rational polynomial at pi (independent Lindemann input); replace with the vetted ExternalPi donor, not a new target axiom.
- `Experimental.P06_15.upstream_unit_geometric`: Geometric expansion of (1+u²)^(-1) on (0,1), before moment integration; does not assert beta evaluations, transcendence or Padé asymptotics.

## Missing domain interfaces

Identification of the beta-one integral with the limit of ordered alternating partial sums and the intended Dirichlet beta value; all-k beta evaluation; algebraic-coefficient independence transfer; quantitative pi transcendence measure; Gram/rank-one construction and exterior Christoffel asymptotics.

## Repair and discharge gates

- For s=1, prove the ordered partial-sum limit equals the actual beta-one integral. An unordered real tsum is not the conditionally convergent alternating series and must not be used to represent beta(1). The s=0 branch is outside this item’s target domain.
- Port the vetted ExternalPi/OddBetaValues donor with matching fingerprints rather than leaving the pi axiom as certification.
- At k=0 use eta(1)=log 2; do not substitute into a totalized vanishing product.
- The printed h^(−2k) exterior rate has an identified repair requirement; formalize the corrected asymptotic before any closure.
- Qualitative pi transcendence does not supply effective C_k or exponent 7.10321.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
