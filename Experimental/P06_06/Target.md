# Experimental manuscript item 6.6

**Theorem 6.6: Generalized multi-weight positive-definite pencil**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_06` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 35.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:multiweight-1v}
Fix an integer $k \ge 1$ and an integer tuple $\mathbf{a} = (a_1, \dots, a_k) \in \mathbb{Z}^k$ with $a_k > 0$. For $K > N \ge 1$ ($h = K - N$), $M \ge 1$, and $R_{i, j}(t) := \frac{D_N(t)^{2M} t^{i+j}}{D_K(t)}$ ($0 \le i, j < h$), define the $h \times h$ Hankel matrix
\[
G_K^{[\mathbf{a}]}(Z) := \left[\sum_{m=1}^k a_m \mu_{X_m}^{(2m+1)}\!\big((-t)^{k-m} R_{i, j}(t)\big)\right]_{0 \le i, j < h}, \qquad Z := \sum_{m=1}^k a_m X_m,
\]
and set $\xi_{\mathbf{a}} := \sum_{m=1}^k a_m \zeta(2m + 1) \in \mathbb{R}$. Then:
\begin{enumerate}
\item At $X_m = \zeta(2m + 1)$ ($1 \le m \le k$, so $Z = \xi_{\mathbf{a}}$), every entry of $G_K^{[\mathbf{a}]}(\xi_{\mathbf{a}})$ admits the exact integral representation
\[
G_K^{[\mathbf{a}]}(\xi_{\mathbf{a}})_{i, j} = \int_0^\infty \frac{D_N(y^2)^{2M} y^{2(i+j)}}{D_K(y^2)} W_{\mathbf{a}}(y)\,dy, \qquad W_{\mathbf{a}}(y) := 2 y^{2k+1} \sum_{l=1}^\infty P_{\mathbf{a}}(l) e^{-2\pi l y},
\]
where $P_{\mathbf{a}}(l) := \sum_{m=1}^k (-1)^{k-m} a_m \frac{(2\pi l)^{2m}}{(2m)!}$.
\item Define the open positivity cone $\mathcal{C}_k^+ := \{\mathbf{a} \in \mathbb{R}^k : P_{\mathbf{a}}(l) > 0 \text{ for all } l \ge 1\}$. For every $\mathbf{a} \in \mathcal{C}_k^+ \cap \mathbb{Z}^k$, the weight $W_{\mathbf{a}}(y)$ satisfies the uniform two-sided comparison $c_1(\mathbf{a}) w_{2k+1}(y) \le W_{\mathbf{a}}(y) \le c_2(\mathbf{a}) w_{2k+1}(y)$ on $(0, \infty)$ with $c_1(\mathbf{a}) := \inf_{l \ge 1} \frac{(2k)! P_{\mathbf{a}}(l)}{(2\pi l)^{2k}} > 0$ and $c_2(\mathbf{a}) := \sup_{l \ge 1} \frac{(2k)! P_{\mathbf{a}}(l)}{(2\pi l)^{2k}} < \infty$. Consequently, $G_K^{[\mathbf{a}]}(\xi_{\mathbf{a}})$ is strictly positive definite, $[Z] G_K^{[\mathbf{a}]}(Z) = M_K^{(2k+1)}$, and all $h$ roots of $\Delta_K^{[\mathbf{a}]}(Z) := \det G_K^{[\mathbf{a}]}(Z)$ are unconditionally real, with signature $(\lfloor h/2 \rfloor, \lceil h/2 \rceil)$ across $\xi_{\mathbf{a}}$ (for $N$ and $h$ of the same parity as in Theorem 3.3(3)) and zero-free disk $|r_j - \xi_{\mathbf{a}}| \ge c_1(\mathbf{a}) \|B_K^{(2k+1)}\|^{-1}$.
\item For every prime $p > \max(|a_1|, \dots, |a_k|, 2k + 3)$, the pullback identity of Lemma 2.2 gives
\[
\sum_{m=1}^k a_m \mu_{X_m}^{(2m+1)}\!\big((-t)^{k-m} R(t)\big) = \sum_{m=1}^k a_m \tau_{X_m}^{(2m+1)}\!\big(x^{2k+1} R(-x^2)\big),
\]
and $\Delta_K^{[\mathbf{a}]}(Z)$ clears to $\mathbb{Z}[Z]$ with the exact same quadratic $p$-adic multiplier rate $A_M^{(2k+1)}$ (up to $e^{O_{\mathbf{a}}(K)}$) as the pure top-weight polynomial $\Delta_K^{(2k+1)}(X)$.
\end{enumerate}
```

## Upstream paper items

- [2.2](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p02-02_construction/Experimental/P02_02/Target.md)
- [3.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p03-01_construction/Experimental/P03_01/Target.md)
- [3.3](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p03-03_construction/Experimental/P03_03/Target.md)
- [4.5](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p04-05_construction/Experimental/P04_05/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Mu.integral_rational_density`
- `ManuscriptChain.Hyperbolic.density_pos`
- `ManuscriptChain.Hyperbolic.summable_exponentialTerm`

## Explicit interface coverage

Encodes the actual finite coefficient polynomial, exponential coupled weight and actual odd-zeta center. Positivity of the cone, uniform comparison constants, pencil identification and arithmetic rates are not axioms.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

No repair is silently substituted for the verbatim target.

Prove both analytic prerequisites; prove the shifted-functional identity in the actual rational domain, discrete positive ratio infimum/supremum and integral comparison. Construct the Z-pencil and its top-weight derivative, transport inertia/radius, then independently establish the claimed actual multiplier rate.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
