# Theorem 6.18: Principal-minor 2-adic integrality law, dyadic height bounds for Zeta--Beta pencils, and multi-weight effective measures

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:principal_minor_2adic}
Let $G_{K}^{[\mathbf{b},\mathbf{a}]}(Z)$ be the coupled multi-weight Zeta--Beta Hankel matrix pencil of Theorem~\ref{thm:multiweight_zeta_beta_1var} on $D_{N}(t)^{2M}/D_{K}(t)$ ($h=K-N$), and for $1\le r\le h$, let $G_{K,r}^{[\mathbf{b},\mathbf{a}]}(Z):=[G_{K}^{[\mathbf{b},\mathbf{a}]}(Z)_{i,j}]_{0\le i,j<r}$ and $\Delta_{K,r}^{[\mathbf{b},\mathbf{a}]}(Z):=\det G_{K,r}^{[\mathbf{b},\mathbf{a}]}(Z)\in\mathbb{Q}[Z]$ denote its $r\times r$ leading principal minor pencil. Then:
\begin{enumerate}
\item[(1)] \textup{(Exact 2-adic disappearance of Euler-number denominators in the sub-threshold principal minors)} Let $r_{\min}:=\min\{1\le m\le k:a_{m}\neq 0\}$. For every integer $1\le r\le\frac{K-2MN-(k-r_{\min})}{2}$ (and for the full $h\times h$ matrix whenever $2MN+2h-2+k-r_{\min}<K$), every shifted rational function $(-t)^{k+1-m}R_{i,j}(t)$ ($0\le i,j<r$, $r_{\min}\le m\le k$) has degree $2MN+i+j+k+1-m<K=\deg D_{K}(t)$, so its polynomial quotient $Q_{i,j}^{(m)}(t)\equiv 0$ vanishes identically. Consequently:
\begin{enumerate}
\item[(i)] No Euler-number monomial moment $\widetilde{\mu}_{Y_{m}}^{(\beta(2m))}(t^{e})$ occurs in $G_{K,r}^{[\mathbf{b},\mathbf{a}]}(Z)$.
\item[(ii)] Because every alternating odd harmonic sum $H_{2j}^{(\beta,2m)}=\sum_{n=0}^{2j-1}(-1)^{n}(2n+1)^{-2m}\in\mathbb{Z}_{2}$ has exclusively odd denominators, the $\beta(2m)$ pole contributions are 2-adically integral (up to the fixed constant $4^{-m}$ in $r_{2j}^{(\beta,2m)}$), so $\Delta_{K,r}^{[\mathbf{b},\mathbf{a}]}(Z)$ clears to $\mathbb{Z}[Z]$ with zero $16^{e}$ dyadic loss at $p=2$, while retaining full hyperbolicity, root interlacing (Theorem~3.4), and positive definiteness $G_{K,r}^{[\mathbf{b},\mathbf{a}]}(\xi_{\mathbf{b},\mathbf{a}})\succ 0$.
\end{enumerate}
\item[(2)] \textup{(Exact dyadic denominator bound at full dimension $h=27n$)} In the weight-5 parameters $K=30n$, $N=3n$, $h=27n$, $2M=6$ ($k=2$), for $b\zeta(5)+a\beta(4)$ ($r_{\min}=2$), the leading $r_{*}\times r_{*}$ principal minor with $r_{*}=6n=\frac{K}{5}$ satisfies $Q_{i,j}^{(2)}(t)\equiv 0$ and is completely free of $16^{-e}$ Euler-number denominators. For the full $27n\times 27n$ determinant $\Delta_{K}^{[b,a]}(Z)$ of Theorem~\ref{thm:zeta5_beta4_coupled}(2), the odd-prime multiplier $m_{K,M}^{(5),\mathrm{odd}}:=\prod_{3\le p\le 2h}p^{-L_{p}^{(5)}(K,M)}$ clears all odd-prime denominators of $S_{K}^{(5)}\Delta_{K}^{[b,a]}(Z)$ into the dyadic ring $\mathbb{Z}[1/2][Z]$ with the exact same odd-prime quadratic exponent as pure $\zeta(5)$, while the 2-adic valuation of the polynomial quotients $Q_{i,j}^{(2)}(t)$ ($\deg Q_{i,j}^{(2)}\le 42n-1$) is bounded by $v_{2}(\widetilde{\mu}_{Y}^{(\beta(4))}(t^{e}))\ge -4e$.
\item[(3)] \textup{(Unconditional irrationality and effective measure $\mu=25687$ for period-$1$ Bose--Einstein cones)} Whenever $a_{1}=\dots=a_{k}=0$ (so the functional is built purely from the period-$1$ Bose--Einstein derivatives $\frac{d^{2m}}{du^{2m}}(e^{2\pi u}-1)^{-1}$, whose analytic singularity at $u=\pm i$ has unit radius $R=1$ and produces pure Bernoulli moments $B_{2e+2}$ whose 2-adic denominator is bounded by $2^{1}=2$ for all $e\ge 0$ by the von Staudt--Clausen theorem), at top weight $2k+1=5$ ($k=2$), for every $(a,b)\in\mathbb{Z}^{2}$ with $b>0$ and $a<\frac{\pi^{2}}{3}b$, the full $27n\times 27n$ normalized determinant $Q_{K}^{[a,b]}(Z)\in\mathbb{Z}[Z]$ is an integer polynomial satisfying $0<Q_{K}^{[a,b]}(b\zeta(5)+a\zeta(3))\le e^{-0.0004K^{2}+O(K)}$ and $|r_{j}-(b\zeta(5)+a\zeta(3))|\ge c_{1}(a,b)e^{-11.411K}$, yielding $|b\zeta(5)+a\zeta(3)-p/q|>q^{-25687}$ for all $q\ge q_{0}(a,b)$.
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 3.4, 4.5, 6.6, 6.14, 6.16. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.Real.D_eq_prod_Icc`
- `ManuscriptChain.Real.D_factorization`

## Typed prerequisite coverage

Concrete original denominator, exact shifted numerator and Euclidean quotient; a typed natural-number degree threshold; actual alternating odd harmonic sums. There is no assumed quotient-zero, dyadic-integrality or effective-measure conclusion.

## Explicit assumptions

No new axioms. The useful current interface consists of concrete data and imported results; missing analytic/arithmetic infrastructure is left open.

## Missing domain interfaces

Port audited donor degree/quotient lemmas after fingerprint verification; beta functional normalization; pole residues; 2-adic ring/valuation and multiplier interfaces; pure-zeta arithmetic transfer.

## Repair and discharge gates

- Check natural-subtraction guards against the exact integer degree inequality before using the threshold.
- Part1 requires an active beta coefficient; rmin is not defined for the all-zero beta tuple.
- Resolve 6.14 normalization before claiming dyadic integrality.
- Part3 is limited to beta coefficients zero and top zeta weight five; it may not be extended to arbitrary zeta–beta mixtures.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
