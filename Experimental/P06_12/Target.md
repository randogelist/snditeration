# Theorem 6.12: Full-dimension sign-flip restoration of positive definiteness and $q$-adic non-vanishing for pure $\beta(4)$

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:beta4_signflip}
Let $w_{\beta(4)}(u)=\frac{\pi}{24}u^{3}\frac{\sinh(\pi u)}{\cosh^{4}(\pi u)}(\cosh^{2}(\pi u)-6)$ on $(0,\infty)$, with unique simple zero $u_{0}=\frac{1}{\pi}\operatorname{arcosh}\sqrt{6}$. For any rational number $r_{0}\in\mathbb{Q}_{>0}$, define the full-dimension $h\times h$ modified Hankel matrix pencil ($h=K-N$)
\[
G_{K}^{(\beta(4),r_{0})}(X):=\left[\mu_{X}^{(\beta(4))}\!\left(\frac{(t-r_{0}^{2})D_{N}(t)^{2m}t^{i+j}}{D_{K}(t)}\right)\right]_{0\le i,j<h},\qquad \Delta_{K}^{(\beta(4),r_{0})}(X):=\det G_{K}^{(\beta(4),r_{0})}(X)\in\mathbb{Q}[X].
\]
Then:
\begin{enumerate}
\item[(1)] \textup{(Preservation of character--Vandermonde sign cancellation and hyperbolicity for all $r_{0}\in\mathbb{Q}_{>0}$)} In the Lagrange basis at $v_{j}=-j^{2}$ ($N<j\le K$), the $X$-derivative matrix $M_{K}^{(\beta(4),r_{0})}:=[X]G_{K}^{(\beta(4),r_{0})}(X)$ factors as
\[
M_{K}^{(\beta(4),r_{0})}=-V\operatorname{diag}\!\Big(\big(j^{2}+r_{0}^{2}\big)\gamma_{j}^{(\beta(4))}\Big)_{N<j\le K}V^{T},
\]
where $\gamma_{j}^{(\beta(4))}>0$ for all $N<j\le K$ by Theorem~\ref{thm:beta4_hyperbolic}(3). Consequently, $-M_{K}^{(\beta(4),r_{0})}\succ 0$ is strictly positive definite, and all $h$ roots of $\Delta_{K}^{(\beta(4),r_{0})}(X)$ are unconditionally real for every $r_{0}\in\mathbb{Q}_{>0}$.
\item[(2)] \textup{(Full-dimension positive definiteness at $X=\beta(4)$ and unilateral root signature)} For every $K>N\ge 1$, there exists an explicit rational approximation $r_{K}\in\mathbb{Q}_{>0}$ to $u_{0}=\frac{1}{\pi}\operatorname{arcosh}\sqrt{6}$ such that $(u^{2}-r_{K}^{2})w_{\beta(4)}(u)>0$ for all $u\in(0,\infty)\setminus[\min(u_{0},r_{K}),\max(u_{0},r_{K})]$ and the full-dimension $h\times h$ evaluation matrix $G_{K}^{(\beta(4),r_{K})}(\beta(4))$ is strictly positive definite ($G_{K}^{(\beta(4),r_{K})}(\beta(4))\succ 0$). Consequently, all $h$ roots of $\Delta_{K}^{(\beta(4),r_{K})}(X)$ are real and lie strictly above $\beta(4)$:
\[
\beta(4)<r_{1}\le r_{2}\le\dots\le r_{h}\qquad (\text{unilateral signature }(0,h)).
\]
\item[(3)] \textup{(Preservation of unconditional $q$-adic non-vanishing)} Under the hypotheses of Theorem~\ref{thm:beta4_qadic} ($q\ge 5$ with $q\equiv 1\pmod{4}$, $m_{q}=(q-1)/4$, $N=2m_{q}$, $K=3m_{q}$, $h=m_{q}$, $2m=2$), for every rational $r_{0}=p_{0}/q_{0}\in\mathbb{Q}_{>0}$ with $q\nmid q_{0}$ and $r_{0}^{2}+j^{2}\not\equiv 0\pmod{q}$ for $2m_{q}<j\le 3m_{q}$, the rational determinant $\Delta_{K}^{(\beta(4),r_{0})}(0)\in\mathbb{Q}$ satisfies the exact $q$-adic valuation
\[
v_{q}\!\left(\Delta_{K}^{(\beta(4),r_{0})}(0)\right)=-3m_{q}<0,
\]
and on $D_{K}^{(\mathrm{odd})}(\tilde{t})$ at $q\equiv 1\pmod{8}$ ($q>7$, $m_{q}'=(q-1)/8$, $q\nmid (r_{0}^{2}+4r^{2})$ for $0\le r<m_{q}'$) satisfies $v_{q}(\Delta_{K}^{(\beta(4),\mathrm{odd},r_{0})}(0))=-(3m_{q}'-2)<0$. In particular, $\Delta_{K}^{(\beta(4),r_{0})}(0)\neq 0$ unconditionally.
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 2.5, 3.1, 6.4, 6.5. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.Real.D`

## Typed prerequisite coverage

Explicit §6.12 analytic weight, actual real integral entries, and a positive reference-root equation. Integrability is isolated without assuming Gram positivity, an effective rational approximation, or valuation preservation.

## Explicit assumptions

- `Experimental.P06_12.upstream_beta_four_moments_integrable`: Polynomial moments of the explicit §6.12 beta-four weight are integrable on the positive half-line; independent of sign-flipped Gram positivity or rational approximation.

## Missing domain interfaces

The beta rational functional and its equality to these integrals; beta derivative diagonalization; a quantitative spectral margin and continuity modulus; an effective rational selection; all q-adic models.

## Repair and discharge gates

- Resolve the manuscript’s missing labels and its incompatible integer-square/odd-square parameter conventions.
- Prove the reference Gram margin and an effective perturbation bound before constructing r_K.
- The q-adic side requires the actual nonzero residue exclusions and both stated prime regimes; do not assume the desired determinant valuation.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
