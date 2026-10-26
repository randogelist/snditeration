# Experimental manuscript item 6.7

**Theorem 6.7: Universal multi-weight two-variable Beukers Krein decomposition**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_07` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 37.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:multiweight-2v}
Fix any integer $k \ge 1$ and any non-zero integer tuple $\mathbf{a} = (a_1, \dots, a_k) \in \mathbb{Z}^k \setminus \{\mathbf{0}\}$. Define the coupled signed measure on $(0, 1)^2$ by
\[
d\Omega_{k, \mathbf{a}}(x_1, x_2) := \sum_{m=1}^k a_m \frac{(-\log(x_1 x_2))^{2m-1}}{(2m)!(1 - x_1 x_2)}\,dx_1\,dx_2,
\]
and for any $h$-dimensional subspace $\mathcal{A} = \{A_0(x), \dots, A_{h-1}(x)\} \subset \mathbb{Q}[x]_{\le K}$ with coefficient matrix $C \in M_{h \times (K+1)}(\mathbb{Q})$, define the $h \times h$ symmetric matrix pencil $G_{\mathcal{A}}^{[\mathbf{a}]}(Z)$ in $Z := \sum_{m=1}^k a_m X_m$ by
\[
G_{\mathcal{A}}^{[\mathbf{a}]}(Z)_{i, j} := \sum_{r=0}^K C_{i, r} C_{j, r}\left(Z - \sum_{m=1}^k a_m H_r^{(2m+1)}\right) + \sum_{0 \le r \neq s \le K} C_{i, r} C_{j, s} \sum_{m=1}^k \frac{a_m}{2m}\frac{H_r^{(2m)} - H_s^{(2m)}}{r - s}.
\]
Set $\xi_{\mathbf{a}} := \sum_{m=1}^k a_m \zeta(2m + 1)$ and $\Delta_{\mathcal{A}}^{[\mathbf{a}]}(Z) := \det G_{\mathcal{A}}^{[\mathbf{a}]}(Z) \in \mathbb{Q}[Z]$. Then:
\begin{enumerate}
\item The $Z$-derivative matrix is $[Z] G_{\mathcal{A}}^{[\mathbf{a}]}(Z) = C C^T \succ 0$, and all $h$ roots of $\Delta_{\mathcal{A}}^{[\mathbf{a}]}(Z)$ are unconditionally real for every $\mathbf{a} \in \mathbb{Z}^k \setminus \{\mathbf{0}\}$.
\item For every $f \in L^2(0, 1)$, setting for $n \ge 0$ and $0 \le \nu \le k - 1$
\[
\Phi_{n, \nu}^{\pm}(x; \mathbf{a}) := x^n \left[ \frac{(-\log x)^\nu}{\nu!} \pm \sum_{m = \max(1, \nu+1)}^k \frac{a_m}{2m}\frac{(-\log x)^{2m - 1 - \nu}}{(2m - 1 - \nu)!} \right],
\]
the quadratic form at $Z = \xi_{\mathbf{a}}$ satisfies the exact Krein decomposition
\[
\iint_{(0,1)^2} f(x_1) f(x_2)\,d\Omega_{k, \mathbf{a}}(x_1, x_2) = \frac{1}{2}\sum_{n=0}^\infty \sum_{\nu=0}^{k-1} \left[ \left(\int_0^1 f(x)\Phi_{n, \nu}^+(x; \mathbf{a})\,dx\right)^2 - \left(\int_0^1 f(x)\Phi_{n, \nu}^-(x; \mathbf{a})\,dx\right)^2 \right],
\]
yielding explicit $h$-dimensional subspaces $\mathcal{A}_+, \mathcal{A}_- \subset \mathbb{Q}[x]_{\le K}$ such that $G_{\mathcal{A}_+}^{[\mathbf{a}]}(\xi_{\mathbf{a}}) \succ 0$ (all roots $r_j < \xi_{\mathbf{a}}$) and $G_{\mathcal{A}_-}^{[\mathbf{a}]}(\xi_{\mathbf{a}}) \prec 0$ (all roots $r_j > \xi_{\mathbf{a}}$).
\item Let $m_* := \max\{1 \le m \le k : a_m \neq 0\}$, and suppose $\sum_{m=1}^k a_m \zeta(2m + 1) = c \in \mathbb{Z}$. For every prime $q > \max(|a_1|, \dots, |a_k|, 2m_* + 3)$, setting $K = 2q - 1$, $h = q$, and $\mathcal{A}_q := \{x^\rho + \kappa_{m_*} x^{\rho+q} : 0 \le \rho < q\}$ (with $\kappa_{m_*} = 1$ if $m_* \ge 2$ and $\kappa_1 = 2$), we have
\[
v_q\big(\Delta_{\mathcal{A}_q}^{[\mathbf{a}]}(c)\big) = -(2m_* + 1) q < 0,
\]
and in particular $\Delta_{\mathcal{A}_q}^{[\mathbf{a}]}(c) \neq 0$.
\end{enumerate}
```

## Upstream paper items

- [5.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-01_construction/Experimental/P05_01/Target.md)
- [5.2](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-02_construction/Experimental/P05_02/Target.md)
- [6.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p06-01_construction/Experimental/P06_01/Target.md)
- [6.3](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p06-03_construction/Experimental/P06_03/Target.md)
- [6.6](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p06-06_construction/Experimental/P06_06/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Real.dualConstant`
- `ManuscriptChain.DualSpectral.coefficientSlope_posDef`
- `ManuscriptChain.Beukers.actual_monomial_krein_bilinear`

## Explicit interface coverage

Encodes the actual signed density, mode density, and normalized affine pencil on finite rational coefficient data. Existing finite spectral algebra is imported. The analytic axioms only support justified interchanges.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

The printed Krein normalization and claimed positive/negative subspaces require independent review. A corrected identity or cone must remain labelled corrected; the literal target is not assumed.

Discharge kernel/summability bounds, identify generalized moments and the exact signed formula including its constants, and prove real roots from independent coefficients. Infinite signed-subspace existence is a separate open problem; no implication from mode independence is assumed. Establish highest-weight p-adic leading blocks before determinant valuation.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
