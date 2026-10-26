# Theorem 5.6 — Weight-seven prime-sum evaluation and pole-ordered refinement

Status: **SOURCE_ONLY_UNCOMPILED**. This is an experimental prerequisite scaffold, not a proof certificate. No Lean/build execution was performed.

## Exact original statement

```tex
\label{thm:zeta7-outer}
Let $\alpha = 3/40, \lambda = 37/40,$ and $H = 1 + 3\alpha = 49/40$. For $y \in [1/3, 37/20]$, define $\tilde{v}(y) := 1 - y\lfloor 1/y \rfloor$, $\tilde{u}(y) := \max(0, \alpha + \tilde{v}(y) - y)$, $\tilde{t}(y) := \min(\alpha, \tilde{v}(y)) + \tilde{u}(y)$, and $\tilde{r}(y) := \max(0, \frac{29}{20} - 3y)$. Set
\[
\widetilde{R}(y) := \begin{cases} 9(1 - y) - 16\alpha - 7\tilde{t}(y) + \min(\tilde{r}(y), y + \tilde{u}(y)), & 1/3 \le y < 1/2, \\ 9(1 - y) - 8\tilde{t}(y) + \min(\tilde{r}(y), y - \alpha + \tilde{u}(y)), & 1/2 \le y < 1, \\ 0, & 1 \le y \le 37/20, \end{cases}
\]
and define the outer prime-sum integrand $T(y) := \widetilde{R}(y) - 2\lambda\lfloor 1/y \rfloor + \sum_{j=1}^7 (2\lambda - jy)_+$. For $x \ge 3$ and $z \in (0, 1/2)$, set $l(x, z) := \lfloor x - z \rfloor + \lfloor x + z \rfloor + 1$, $b(x, z) := 4 l(\alpha x, z)$, $T_x := \lfloor 2Hx \rfloor$, $s_x := Hx - T_x/2$, $q_x := \lfloor 2x \rfloor$, $n_+ := x - q_x/2$, and define the inner limiting function $R(x) := -\Gamma(x) - \mathcal{N}(x)$, where
\begin{align*}
\Gamma(x) &:= \int_0^{1/2} (T_x - b(x,z))(T_x + b(x,z) - l(x,z) - 7)\,dz + s_x(2T_x - q_x - 7) + (s_x - n_+)_+, \\
\mathcal{N}(x) &:= 2\lambda x \lfloor x \rfloor - 16\lambda x \lfloor \alpha x \rfloor - 2\lfloor 2\lambda x \rfloor \lambda x + \frac{\lfloor 2\lambda x \rfloor(\lfloor 2\lambda x \rfloor + 1)}{2}.
\end{align*}
Then:
\begin{enumerate}
\item $T(y)$ is continuous on $[1/3, 1/2)$ and on $[1/2, 1)$, and its exact integral over $[1/3, 37/20]$ is
\begin{equation}\label{eq:Iout-exact}
I_{\mathrm{out}} := \int_{1/3}^{37/20} T(y)\,dy = \frac{453803}{288000} \approx +1.57570486.
\end{equation}
\item The inner tail integral satisfies $\int_{20}^\infty \frac{R(x)}{x^3}\,dx \le A_0 := -\frac{33104}{576000} \approx -0.05747222$.
\item In the inner prime range $K/M < p \le K/3$ ($m_p = (p-1)/2$), let $k_{a, 1} > k_{a, 2} > \dots > k_{a, s_a}$ ($s_a = l_K(a) - l_N(a)$) be the poles of $D_{\mathrm{tail}}(t)$ in residue class $a \pmod p$ in decreasing order. Replacing $(t + a^2)^i$ in the local basis $E_{a,i}(t) = \prod_{0 \le c < a}(t+c^2)^{L_c} (t+a^2)^i$ by $\prod_{\nu=1}^{\min(i, s_a - 2)} (t + k_{a,\nu}^2) (t + a^2)^{\max(0, i - (s_a - 2))}$ upgrades the local half-weights from $w_{a, i} = i + 4l_N(a) - (l_K(a) + 6)/2$ to
\[
\widetilde{w}_{a, i} = \begin{cases} i + 4l_N(a) - \dfrac{l_K(a) + 6}{2}, & 0 \le i < L_a - 2, \\[6pt] i + 4l_N(a) - \dfrac{l_K(a)}{2}, & L_a - 2 \le i < L_a, \end{cases}
\]
increasing the inner determinant valuation bound $\gamma_p^{\mathrm{in}} = 2\sum_{a=0}^{m_p} \sum_{i=0}^{L_a - 1} w_{a, i}$ by $6(p - 1)$, which increases $\Gamma(x) = \lim_{p\to\infty} \gamma_p^{\mathrm{in}} / p$ by $+6$ for all $x \ge 3$ and reduces $\int_3^\infty \frac{R(x)}{x^3}\,dx$ by $\int_3^\infty \frac{6}{x^3}\,dx = \frac{1}{3}$.
\end{enumerate}
```

## Imported verified source boundary

`Zetahyperbolic` at `randogelist/snditeration@3b184ba109f065d973957a5735fb590fea4b0e35`; Lean 4.33.0 and pinned Mathlib. Existing proved components are imported, not re-axiomatized. Current source/audit and historical target-specific receipts govern those imports; this experimental extension has not compiled.

## Typed prerequisite coverage

Actual outer and inner real functions are defined verbatim; axioms cover regularity/convergence only. None of the three printed numeric/arithmetic conclusions is assumed.

- `Experimental.P05_06.outerT_integrable`: Integrability of the literal floor/min/max outer integrand on the printed compact interval.
- `Experimental.P05_06.inner_tail_integrable`: Absolute integrability of the literal inner R(x)/x^3 on (20,∞); no sign or constant bound.

## Remaining object-interface and proof work

Construct and verify the full floor-function interval partition, continuity claims and exact integration; derive a rigorous periodic-primitive tail majorant proving the signed inequality; build actual pole classes, ordered replacement polynomials, invertible local basis transformation and q-adic determinant valuation estimates.

## Repair gate

Table arithmetic alone is not a partition proof. Audit floor endpoints, survivor classes and replacement ranges. Imported 5.4 only applies to simple pole pairs and cannot silently supply higher-order residue claims.

## Discharge obligations

Replace outerT_integrable by finite-piece regularity proof and inner_tail_integrable by a proved absolute majorant. These are deliberately weaker than the final integral value and inequality.

## Dependency identifiers

`P05_04`, `P05_05_SIMPLE_POLE_SCOPE`.
