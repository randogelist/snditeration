# Theorem 5.2 — Dual hyperbolicity and Krein-space decomposition of the two-variable $\zeta(7)$ pencil

Status: **SOURCE_ONLY_UNCOMPILED**. This is an experimental prerequisite scaffold, not a proof certificate. No Lean/build execution was performed.

## Exact original statement

```tex
\label{thm:dual-pencil}
Let $K \ge h \ge 1$ be integers, and let $\mathcal{A} = \{A_0(x), \dots, A_{h-1}(x)\} \subset \QQ[x]_{\le K}$ be any $h$ linearly independent polynomials with coefficient matrix $C = \big([x^r] A_i(x)\big)_{0 \le i < h, \, 0 \le r \le K} \in M_{h \times (K+1)}(\QQ)$. Define the $h \times h$ symmetric matrix pencil $G_{\mathcal{A}}^{(7)}(X)$ by
\begin{equation}\label{eq:GA7-pencil}
G_{\mathcal{A}}^{(7)}(X)_{i, j} := \sum_{r=0}^K C_{i, r} C_{j, r} \big(X - H_r^{(7)}\big) + \frac{1}{6} \sum_{0 \le r \neq s \le K} C_{i, r} C_{j, s} \frac{H_r^{(6)} - H_s^{(6)}}{r - s}.
\end{equation}
Then:
\begin{enumerate}
\item The $X$-derivative matrix $M_{\mathcal{A}}^{(7)} := [X] G_{\mathcal{A}}^{(7)}(X) = C C^T$ is strictly positive definite, and $\Delta_{\mathcal{A}}^{(7)}(X) := \det G_{\mathcal{A}}^{(7)}(X) \in \QQ[X]$ has exact degree $h$ with all $h$ roots real: $r_j = \zeta(7) - \gamma_j \in \RR$, where $\gamma_1, \dots, \gamma_h \in \RR$ are the eigenvalues of $L^{-1} G_{\mathcal{A}}^{(7)}(\zeta(7)) (L^{-1})^T$ ($C C^T = L L^T$).
\item For any $f \in L^2(0, 1)$, setting $\psi_{m, \nu}^{\pm}(x) := x^m \big((-\log x)^\nu \pm (-\log x)^{5-\nu}\big)$ ($m \ge 0, \nu \in \{0, 1, 2\}$), the bilinear form at $X = \zeta(7)$ satisfies the exact Krein decomposition
\begin{equation}\label{eq:Krein-decomp}
\iint_{(0, 1)^2} f(x_1) f(x_2) \, d\Omega_7(x_1, x_2) = \frac{1}{1440} \sum_{m=0}^\infty \sum_{\nu=0}^2 \binom{5}{\nu} \left[ \left(\int_0^1 f(x) \psi_{m, \nu}^+(x)\,dx\right)^2 - \left(\int_0^1 f(x) \psi_{m, \nu}^-(x)\,dx\right)^2 \right].
\end{equation}
\item For every integer $h \ge 1$ and every truncation $M \ge h$, there exist explicit $h$-dimensional polynomial subspaces $\mathcal{A}_+, \mathcal{A}_- \subset \QQ[x]_{\le K}$ such that $G_{\mathcal{A}_+}^{(7)}(\zeta(7)) \succ 0$ (all roots of $\Delta_{\mathcal{A}_+}^{(7)}(X)$ strictly less than $\zeta(7)$) and $G_{\mathcal{A}_-}^{(7)}(\zeta(7)) \prec 0$ (all roots strictly greater than $\zeta(7)$).
\end{enumerate}
```

## Imported verified source boundary

`Zetahyperbolic` at `randogelist/snditeration@3b184ba109f065d973957a5735fb590fea4b0e35`; Lean 4.33.0 and pinned Mathlib. Existing proved components are imported, not re-axiomatized. Current source/audit and historical target-specific receipts govern those imports; this experimental extension has not compiled.

## Typed prerequisite coverage

Only an analytic prerequisite for part (2). Parts (1) and (2) already have imported finite support; no whole printed theorem is asserted.

- `Experimental.P05_02.actual_density_memLp_two`: The actual printed unit-square Beukers density is square-integrable; a Hilbert-Schmidt regularity input, not the L2 Krein identity or cone existence.

## Remaining object-interface and proof work

Construct the L2 operator API, prove representative independence and boundedness; identify the finite coefficient form with the actual polynomial-product double integral; extend by density; establish signed-mode summability. Part (1) still needs the precise rational-polynomial-independence interface if not imported.

## Repair gate

Part (3) cannot be admitted with its literal universal fixed-K quantifiers: preserve the dimension gate 2h≤K+1 and require an explicitly repaired sufficiently-large-K statement, followed by genuine infinite-tail control. No cone-existence axiom is introduced.

## Discharge obligations

Replace actual_density_memLp_two by an explicit logarithmic integral estimate for Beukers.density on the actual squareMeasure. Then separately discharge mode bounds and convergence; this assumption alone is not complete closure.

## Dependency identifiers

`P05_01`, `P05_02_FINITE_SPECTRUM`, `P05_02_MONOMIAL_KREIN`.
