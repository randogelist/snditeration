# Experimental manuscript item 6.3

**Theorem 6.3: Unconditional $q$-adic non-vanishing and explicit positive-cone approximations for $G_{\mathcal{A}}^{(7)}(X)$**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_03` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 32.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:zeta7-nonvanish}
Let $G_{\mathcal{A}}^{(7)}(X)$ be the two-variable Beukers matrix pencil of Theorem 5.2.
\begin{enumerate}
\item \emph{(Unconditional $q$-adic non-vanishing)} Let $q \ge 5$ be any prime, and set $K = 2q - 1$ and $h = q$. For the $q$-dimensional polynomial basis $\mathcal{A}_q := \{A_\rho(x) := x^\rho + x^{\rho + q} : 0 \le \rho < q\} \subset \mathbb{Z}[x]_{\le 2q-1}$, the rational determinant $\Delta_{\mathcal{A}_q}^{(7)}(0) = \det G_{\mathcal{A}_q}^{(7)}(0) \in \mathbb{Q}$ satisfies the exact $q$-adic valuation
\[
v_q\big(\Delta_{\mathcal{A}_q}^{(7)}(0)\big) = -7 q < 0.
\]
In particular, $\Delta_{\mathcal{A}_q}^{(7)}(0) \neq 0$, and $\Delta_{\mathcal{A}_q}^{(7)}(a/b) \neq 0$ for every rational $a/b \in \mathbb{Q}$ with $q \nmid b$.
\item \emph{(Explicit positive-cone basis with exponential decay)} Fix an integer $h \ge 1$, set $m_0 := 2h$ and $K := 7h$, and consider the $4h$-dimensional rational polynomial space $\mathcal{W}_K := \{x^{m_0}(1 - x)^h Q(x) : Q(x) \in \mathbb{Q}[x]_{< 4h}\} \subset \mathbb{Q}[x]_{\le K}$. Define the explicit rational subspace
\[
\mathcal{V}_K^+ := \left\{ P(x) \in \mathcal{W}_K : \int_0^1 P(x)\psi_{m, \nu}^-(x)\,dx = 0 \;\text{ for all }\; 0 \le m < h, \; \nu \in \{0, 1, 2\} \right\},
\]
where $\psi_{m, \nu}^-(x) = x^m((-\log x)^\nu - (-\log x)^{5-\nu})$ is as in Theorem 5.2(2). Then $\dim_{\mathbb{Q}} \mathcal{V}_K^+ \ge h$, and for any $h$-dimensional basis $\mathcal{A}_+^{(K)} = \{A_0(x), \dots, A_{h-1}(x)\} \subset \mathcal{V}_K^+$ normalized so that $A_i(x) = x^{m_0}(1 - x)^h Q_i(x)$ has $\sum_{j=0}^{4h-1} |[x^j] Q_i(x)| \le 1$, the evaluation matrix $G_{\mathcal{A}_+^{(K)}}^{(7)}(\zeta(7))$ is strictly positive definite and satisfies
\[
0 < \Delta_{\mathcal{A}_+^{(K)}}^{(7)}(\zeta(7)) \le (4^{-2h} h^{-6})^h.
\]
\end{enumerate}
```

## Upstream paper items

- [5.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-01_construction/Experimental/P05_01/Target.md)
- [5.2](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-02_construction/Experimental/P05_02/Target.md)
- [6.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p06-01_construction/Experimental/P06_01/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Real.dualEntry`
- `ManuscriptChain.Beukers.actual_monomial_krein_bilinear`
- `ManuscriptChain.Beukers.polynomialMomentForm_eq_krein`

## Explicit interface coverage

The q-dimensional part uses the actual rational dual pencil and explicit basis coefficients. The disputed cone has explicit polynomial/mode definitions for inspection only.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

BLOCKED_LITERAL_PART_2: the repository documents an actual h=4 negative-direction counterexample. Neither positive definiteness nor determinant decay is assumed. A corrected target needs an explicit separately approved statement.

For part (1), derive the scaled entry matrix and its reduction from the harmonic residual, then prove determinant valuation and rational-center nonvanishing. For part (2), do not attempt a closure of the literal claim until the documented h=4 counterexample and a replacement statement are reconciled. Finite mode annihilation is not infinite-tail positivity.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
