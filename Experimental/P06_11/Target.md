# Theorem 6.11: The $p^{-(2k-1)}$ distribution growth law and 2-adic polynomial-quotient obstruction for $\beta(2k)$

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:beta_obstruction}
Consider the single-variable odd-square Hankel construction $G_{K}^{(\beta(2k),\mathrm{odd})}(X)$ on the kernel $D_{N}^{(\mathrm{odd})}(t)^{2m}/D_{K}^{(\mathrm{odd})}(t)$ with $h=K-N=\lambda K$ and $N=\alpha K$ ($\alpha+\lambda=1$, $m\ge 1$).
\begin{enumerate}
\item[(1)] \textup{(Linear growth of the odd-prime denominator exponent in $k$)} Under the odd-pole pullback $\mu_{X}^{(\beta(2k),\mathrm{odd})}(R(t))=\tau_{X}^{(\beta,2k)}(x^{2k-1}R(-x^{2}))$ at poles $x=2r+1$ ($r\in\mathbb{Z}$), the Euler-polynomial multiplication identity $E_{n}(px)=p^{n}\sum_{a=0}^{p-1}(-1)^{a}E_{n}(x+\frac{a}{p})$ for every odd prime $p\ge 3$ induces a local $p$-adic distribution relation with prefactor $p^{-(2k-1)}$ across the residue classes $2r+1\equiv 2a+1\pmod{2p}$. In the inner prime range $K/M<p\le K/3$ ($x=K/p\ge 3$), each nonzero square class $a^{2}\pmod{p}$ ($1\le a\le\frac{p-1}{2}$) contains $l_{K}^{(\mathrm{odd})}(a)=2x+O(1)$ poles of $D_{K}^{(\mathrm{odd})}(t)$ and $l_{N}^{(\mathrm{odd})}(a)=2\alpha x+O(1)$ roots of $D_{N}^{(\mathrm{odd})}(t)$, with local half-weights shifted by $-\frac{2k-1}{2}$:
\[
w_{a,i}^{(\beta,2k)}=i+m\,l_{N}^{(\mathrm{odd})}(a)-\left\lceil\frac{l_{K}^{(\mathrm{odd})}(a)+2k-1}{2}\right\rceil\qquad (0\le i<L_{a}:=l_{K}^{(\mathrm{odd})}(a)-l_{N}^{(\mathrm{odd})}(a)).
\]
Consequently, for fixed $(\alpha,2m)$, the odd-prime denominator exponent $A_{M}^{(\beta,2k)}$ grows strictly and linearly with $k\ge 1$:
\[
A_{M}^{(\beta,2k)}-A_{M}^{(\beta,2)}=2(k-1)\lambda\int_{3}^{M}\frac{dx}{x^{2}}+O\!\left(\frac{k}{M^{2}}\right)=\frac{2(k-1)\lambda}{3}+O\!\left(\frac{k}{M}\right)>0,
\]
whereas under the macroscopic scaling $t=4K^{2}x$ ($y=2K\sqrt{x}$), the archimedean upper-bound rate
\[
\overline{U}^{(\beta,2k)}=\overline{U}^{(\beta)}(\alpha,2m)=\sup_{\substack{\mu\ge 0\\\mu(\mathbb{R}_{\ge 0})=\lambda}}\left[\iint\log|x-z|\,d\mu(x)\,d\mu(z)-\int_{0}^{\infty}\big(\pi\sqrt{x}+J_{1}(x)-2mJ_{\alpha}(x)\big)\,d\mu(x)\right]+2(2m-1)\alpha\lambda\log 2
\]
is independent of $k$. In particular, $A_{M}^{(\beta,2k)}+\overline{U}^{(\beta,2k)}\to +\infty$ as $k\to\infty$.
\item[(2)] \textup{(The 2-adic polynomial-quotient obstruction at $p=2$)} Under the substitution $t=4w-1$ ($w=(t+1)/4$), every odd-square factor satisfies $t+(2j+1)^{2}=4(w+j(j+1))$ with $j(j+1)\in 2\mathbb{Z}$. In the unitriangular 2-adic basis $\phi_{i}(t):=(t+1)^{i}=(4w)^{i}$, the pole part of $\mu_{X}^{(\beta(2k),\mathrm{odd})}(D_{N}^{(\mathrm{odd})}(t)^{2m}\phi_{i}(t)\phi_{j}(t)/D_{K}^{(\mathrm{odd})}(t))$ carries the 2-adic factor $4^{2mN+i+j-K+1}$. However, for every entry $(i,j)$ with $d_{i,j}:=2mN+i+j-K\ge 0$, the polynomial quotient $Q_{i,j}(t)\in\mathbb{Z}[t]$ in the Euclidean division $D_{N}^{(\mathrm{odd})}(t)^{2m}(t+1)^{i+j}=Q_{i,j}(t)D_{K}^{(\mathrm{odd})}(t)+R_{i,j}(t)$ satisfies
\[
Q_{i,j}(t)=4^{d_{i,j}}\widetilde{Q}_{i,j}\!\left(\frac{t+1}{4}\right)=(t+1)^{d_{i,j}}+\sum_{e=0}^{d_{i,j}-1}4^{d_{i,j}-e}\tilde{q}_{i,j;e}(t+1)^{e}\qquad (\tilde{q}_{i,j;e}\in\mathbb{Z}).
\]
Since $E_{0}=1$ and $E_{2r}\equiv 1\pmod{2}$ for all $r\ge 1$, we have $\mu_{X}^{(\beta(2k),\mathrm{odd})}((t+1)^{e})=\sum_{r=0}^{e}\binom{e}{r}\mu_{X}^{(\beta(2k),\mathrm{odd})}(t^{r})\equiv E_{0}=1\pmod{2}$ for all $e\ge 0$ whenever $k$ is a power of $2$ (and at $e=0$ for all $k\ge 1$), so $v_{2}(\mu_{X}^{(\beta(2k),\mathrm{odd})}(Q_{i,j}(t)))=0$ whenever $d_{i,j}=0$, preventing the pole factor $4^{(2m-1)\alpha\lambda K^{2}}$ from dividing the polynomial part at $p=2$.
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 2.1, 6.4, 6.5. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.Real.D`

## Typed prerequisite coverage

Actual finite odd harmonic sums, odd-square denominator, Euclidean polynomial quotient and a concrete Euler-polynomial definition. Only the independent Euler shift identity is assumed.

## Explicit assumptions

- `Experimental.P06_11.upstream_euler_shift`: Euler polynomial shift identity E_n(x+1)+E_n(x)=2x^n on the explicit finite Bernoulli definition; an independent prerequisite for the distribution calculation.

## Missing domain interfaces

No local p-adic functional, Euler-number secant normalization, half-weight sum, limiting prime-sum rate or valuation proof has been encoded.

## Repair and discharge gates

- Prove the p-distribution formula from the finite Euler definition before using the exponent shift.
- Reconcile Euler polynomial coefficients with the manuscript secant Euler-number convention.
- Discharge all quotient and residue valuations on these actual polynomials; do not infer them from scaling alone.
- Check the strict linear-growth formulation at k=1 and all error-term quantifiers before adopting a repaired target.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
