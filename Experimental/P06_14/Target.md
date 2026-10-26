# Theorem 6.14: Even-pole scaling via $\cosh(2\pi v)$ and coupled positive-definite pencils for $b\zeta(5)+a\beta(4)$ and $b\zeta(5)-a\beta(2)$

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:zeta5_beta4_coupled}
For each integer $r\ge 1$, define on $v\in(0,\infty)$ the scaled weight and rational functional
\[
\widetilde{w}_{\beta(2r)}(v):=-4\,w_{\beta(2r)}(2v)=\frac{2^{5-4r}}{(2r-1)!\pi^{2r-1}}v^{2r-1}(-1)^{r-1}\frac{d^{2r-1}}{dv^{2r-1}}\!\left(\frac{\pi}{2\cosh(2\pi v)}\right),\qquad \widetilde{\mu}_{Y}^{(\beta(2r))}(R(t)):=-\mu_{Y}^{(\beta(2r))}(R(4t)).
\]
Then:
\begin{enumerate}
\item[(1)] \textup{(Constant $+1$ sign at integer-square poles $t=-j^{2}$)} For every integer $e\ge 0$, every positive integer $j\ge 1$, and every rational function $R(t)$ with simple poles among $\{-j^{2}:j\ge 1\}$, we have $\widetilde{\mu}_{\beta(2r)}^{(\beta(2r))}(R(t))=\int_{0}^{\infty}R(v^{2})\widetilde{w}_{\beta(2r)}(v)\,dv$, with
\[
\widetilde{\mu}_{Y}^{(\beta(2r))}(t^{e})=\frac{(-1)^{r+e}E_{2e}}{16^{e}}\binom{2e+2r-1}{2r-1}\in\mathbb{Z}\!\left[\frac{1}{2}\right],\qquad \widetilde{\mu}_{Y}^{(\beta(2r))}\!\left(\frac{1}{t+j^{2}}\right)=(2j)^{2r-2}\big(Y-H_{2j}^{(\beta,2r)}\big)-\frac{1}{4}r_{2j}^{(\beta,2r)}.
\]
In particular, on the standard Riemann zeta denominator $D_{K}(t)=\prod_{j=1}^{K}(t+j^{2})$, applying $4^{1-r}\widetilde{\mu}_{Y}^{(\beta(2r))}$ to $(-t)^{k+1-r}R(t)$ produces at every pole $t=-j^{2}$ ($1\le j\le K$) the residue $+j^{2k}(Y-H_{2j}^{(\beta,2r)})+\tilde{r}_{j,k,r}$ with constant $+1$ sign and homogeneous prefactor $j^{2k}$ identical to $\mu_{X}^{(2k+1)}((t+j^{2})^{-1})$, while every monomial moment has zero odd-prime denominators ($v_{p}=0$ for all odd primes $p\ge 3$).
\item[(2)] \textup{(Coupled $(\zeta(5),\beta(4))$ and $(\zeta(5),\beta(2))$ positive-definite pencils on $D_{K}(t)$)} Set $C_{4}:=\sup_{v>0}\frac{v^{2}|\widetilde{w}_{\beta(4)}(v)|}{w_{5}(v)}<\infty$ and $C_{2}:=\sup_{v>0}\frac{v^{4}|\widetilde{w}_{\beta(2)}(v)|}{w_{5}(v)}<\infty$ (where $-\widetilde{w}_{\beta(2)}(v)=8\pi\frac{v\sinh(2\pi v)}{\cosh^{2}(2\pi v)}>0$ for all $v>0$). Then:
\begin{enumerate}
\item[(i)] For all integers $(a,b)\in\mathbb{Z}^{2}$ with $b>0$ and $|a|<(4/C_{4})b$, the coupled functional $b\mu_{X}^{(5)}(R(t))+\frac{a}{4}\widetilde{\mu}_{Y}^{(\beta(4))}(-tR(t))$ on $R_{i,j}(t)=\frac{D_{N}(t)^{6}t^{i+j}}{D_{K}(t)}$ collapses to a single-variable matrix pencil in $Z:=bX+aY$ with derivative $[Z]G_{K}(Z)=M_{K}^{(5)}$, strictly positive weight $bw_{5}(v)+\frac{a}{4}v^{2}\widetilde{w}_{\beta(4)}(v)>0$ on $(0,\infty)$, unconditional real-rootedness of all $h$ roots, signature $(\lfloor h/2\rfloor,\lceil h/2\rceil)$, and exponential zero-free disk $|r_{j}-(b\zeta(5)+a\beta(4))|\ge c_{1}(a,b)e^{-11.411K}$.
\item[(ii)] For all integers $(a,b)\in\mathbb{Z}^{2}$ with $b>0$ and $a>-(1/C_{2})b$ (including all $a\ge 0$, $b>0$), the differentially shifted functional $b\mu_{X}^{(5)}(R(t))-a\widetilde{\mu}_{Y}^{(\beta(2))}(t^{2}R(t))$ collapses to a single-variable matrix pencil in $Z:=bX-aY$ with derivative $[Z]G_{K}(Z)=M_{K}^{(5)}$, strictly positive weight $bw_{5}(v)-av^{4}\widetilde{w}_{\beta(2)}(v)>0$ on $(0,\infty)$, unconditional real-rootedness, signature $(\lfloor h/2\rfloor,\lceil h/2\rceil)$, and exponential zero-free disk $|r_{j}-(b\zeta(5)-a\beta(2))|\ge\tilde{c}_{1}(a,b)e^{-11.411K}$.
\end{enumerate}
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 3.1, 4.4, 6.4. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.UnitLogMoments.integral_pow_log`
- `ManuscriptChain.Hyperbolic.density_pos`

## Typed prerequisite coverage

Concrete beta series/finite harmonics, an explicit scaling operator, and the independent secant transform. No equivalence between conflicting printed normalizations is assumed.

## Explicit assumptions

- `Experimental.P06_14.upstream_sech_cosine_transform`: Cosine transform of the genuine hyperbolic secant; an upstream analytic identity independent of the requested scaled beta pole functional and coupled pencil.

## Missing domain interfaces

A coherent unscaled beta rational functional, the exact change of variables and Jacobian, its monomial and pole formulas, comparison constants C2/C4 and the actual coupled matrix.

## Repair and discharge gates

- The source proof itself contains a “Wait” normalization correction and obtains a factor 2 differing from the displayed monomial formula. Resolve definitions and Jacobian first.
- Do not combine −μ(R(4t)) with an incompatible −4w(2v) formula as axioms.
- Cone positivity, pole alignment and integer arithmetic must use one repaired convention throughout.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
