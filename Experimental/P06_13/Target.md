# Theorem 6.13: Central-factorial secant differential identity, Laplace mode annihilation, and unilateral $(h,0)$ root signature for all $k\ge 1$

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:beta_central_factorial}
For every integer $k\ge 1$, let $c_{k,m}>0$ ($1\le m\le k$, with $c_{k,k}:=1$) denote the central factorial numbers (elementary symmetric polynomials in the first $k-1$ odd squares $\{1^{2},3^{2},\dots,(2k-3)^{2}\}$), defined by
\[
\prod_{r=1}^{k-1}\big(v-(2r-1)^{2}\big)=\sum_{m=1}^{k}(-1)^{k-m}c_{k,m}v^{m-1},
\]
and define the $(2k-1)$-th order differential operator $\mathcal{L}_{k}:=-\frac{d}{dz}\prod_{r=1}^{k-1}\big((2r-1)^{2}-\frac{d^{2}}{dz^{2}}\big)$. Then:
\begin{enumerate}
\item[(1)] \textup{(Exact closed-form positivity and Laplace mode annihilation for all $k\ge 1$)} For all $z>0$,
\begin{equation}\label{eq:secant_power_id}
\mathcal{L}_{k}\!\left(\frac{1}{2\cosh z}\right)=\frac{(2k-1)!\sinh z}{2\cosh^{2k}z}=\sum_{l=k-1}^{\infty}(-1)^{l}(2l+1)\prod_{r=1}^{k-1}\big((2l+1)^{2}-(2r-1)^{2}\big)e^{-(2l+1)z}>0.
\end{equation}
In particular, the first $k-1$ Laplace modes $l=0,1,\dots,k-2$ vanish identically, and the strictly positive weight $W_{k}^{+}(u):=4^{1-k}\pi u^{2k-1}\frac{\sinh(\pi u)}{\cosh^{2k}(\pi u)}>0$ on $(0,\infty)$ decays as $u\to\infty$ at the accelerated exponential rate $O\big(u^{2k-1}e^{-(2k-1)\pi u}\big)$.
\item[(2)] \textup{(Simultaneous positive definiteness of $G_{K}$ and $M_{K}$ and unilateral $(h,0)$ root signature)} Set $\tilde{c}_{k,m}:=\frac{(2m-1)!}{(2k-1)!}\big(\frac{\pi}{2}\big)^{2k-2m}c_{k,m}>0$ ($1\le m\le k$, so $\tilde{c}_{k,k}=1$). For $R_{i,j}(t)=\frac{D_{N}(t)^{2M}t^{i+j}}{D_{K}(t)}$ ($0\le i,j<h$), define the coupled $h\times h$ Hankel matrix pencil
\[
G_{K}^{(k)}(Z):=\left[\sum_{m=1}^{k}\tilde{c}_{k,m}\mu_{X_{m}}^{(\beta(2m))}\!\big((-t)^{k-m}R_{i,j}(t)\big)\right]_{0\le i,j<h},\qquad Z:=\sum_{m=1}^{k}\tilde{c}_{k,m}X_{m},
\]
and set $\Xi_{k}:=\sum_{m=1}^{k}\tilde{c}_{k,m}\beta(2m)$. Then at $X_{m}=\beta(2m)$ ($Z=\Xi_{k}$), both the evaluation matrix $G_{K}^{(k)}(\Xi_{k})=\big[\int_{0}^{\infty}R_{i,j}(u^{2})W_{k}^{+}(u)\,du\big]_{0\le i,j<h}\succ 0$ and the $Z$-derivative matrix $[Z]G_{K}^{(k)}(Z)=M_{K}^{(\beta(2k))}\succ 0$ are simultaneously strictly positive definite. Consequently:
\begin{enumerate}
\item[(i)] The relative matrix $B_{K}^{(k)}:=G_{K}^{(k)}(\Xi_{k})^{-1/2}M_{K}^{(\beta(2k))}G_{K}^{(k)}(\Xi_{k})^{-1/2}\succ 0$ is strictly positive definite (signature $(h,0)$).
\item[(ii)] All $h$ roots $r_{1},\dots,r_{h}$ of $\det G_{K}^{(k)}(Z)=0$ are real and lie strictly below $\Xi_{k}$:
\[
r_{1}\le r_{2}\le\dots\le r_{h}<\Xi_{k}\qquad (\text{unilateral signature }(h,0)).
\]
\item[(iii)] In the shifted variable $Y=Z-\Xi_{k}$, all $h+1$ Taylor coefficients of $\det G_{K}^{(k)}(\Xi_{k}+Y)=\sum_{m=0}^{h}e_{m}Y^{m}$ are strictly positive ($e_{m}>0$ for all $0\le m\le h$) and satisfy strict Newton log-concavity $\tilde{e}_{m}^{2}>\tilde{e}_{m-1}\tilde{e}_{m+1}$ ($\tilde{e}_{m}:=e_{m}/\binom{h}{m}$) for all $1\le m\le h-1$ with zero internal zeros.
\end{enumerate}
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 6.4. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.Hyperbolic.summable_exponentialTerm`

## Typed prerequisite coverage

The concrete secant kernel, its base series, and the finite differential operator are typed. Existing exponential-series summability is available as a starting estimate.

## Explicit assumptions

- `Experimental.P06_13.upstream_secant_laplace_expansion`: Base undifferentiated expansion 1/(2 cosh z)=sum (-1)^n exp(-(2n+1)z) for z>0; no central-factorial or differentiated conclusion is assumed.

## Missing domain interfaces

Port the already reported donor finite operator proof after checking its source/dependency identity; establish local uniform differentiated convergence; construct the actual coupled beta pencil.

## Repair and discharge gates

- The printed differentiated series has a missing global (−1)^(k−1) factor. Do not assume the literal printed series.
- The endpoint is Xi_k, a beta combination with pi-dependent coefficients; this is not an individual beta irrationality theorem.
- Strict Newton inequalities need their correct multiplicity/nondegeneracy conditions, not genericity.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
