# Experimental manuscript item 6.4

**Theorem 6.4: Character--Vandermonde sign cancellation and unconditional hyperbolicity for $\beta(4)$**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_04` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 33.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:beta4-hyperbolic}
Fix integers $K > N \ge 0$ ($h = K - N$) and $m \ge 1$. Then:
\begin{enumerate}
\item At $X = \beta(4)$, for every rational function $R(t)$ in the domain of $\mu_X^{(\beta(4))}$,
\[
\mu_{\beta(4)}^{(\beta(4))}(R(t)) = \int_0^\infty R(y^2) w_{\beta(4)}(y)\,dy, \qquad w_{\beta(4)}(y) := -\frac{y^4}{6\pi^2}\frac{d^3}{dy^3}\!\left(\frac{\pi}{2\cosh(\pi y / 2)}\right).
\]
Furthermore, coupling $\beta(4)$ with $-\frac{\pi^2}{24}\beta(2)$ via the differential operator $-\frac{4}{\pi^2}\frac{d^3}{dy^3} + \frac{d}{dy}$ yields the strictly positive single-variable weight
\[
W_\beta^+(y) := \frac{y^4}{24}\left(-\frac{4}{\pi^2}\frac{d^3}{dy^3} + \frac{d}{dy}\right)\left(\frac{1}{2\cosh(\pi y / 2)}\right) = \frac{\pi^2}{16}\frac{y^4 \sinh(\pi y / 2)}{\cosh^4(\pi y / 2)} > 0 \qquad (y > 0).
\]
\item In the Lagrange basis at the odd-square poles $v_j = -(2j + 1)^2$ ($N \le j < K$), the $X$-derivative matrix $M_K^{(\beta(4))} := [X] G_K^{(\beta(4))}(X)$ factors as $M_K^{(\beta(4))} = V_{\mathrm{odd}} \operatorname{diag}\big(\gamma_j^{(\beta(4))}\big)_{N \le j < K} V_{\mathrm{odd}}^T$, where $V_{\mathrm{odd}} = (v_j^i)_{0 \le i < h, \, N \le j < K}$ and
\[
\gamma_j^{(\beta(4))} := \frac{(2j + 1)^3 (-1)^j D_N^{(\mathrm{odd})}(-(2j + 1)^2)^{2m-1}}{D_{\mathrm{tail}}^{(\mathrm{odd})\prime}(-(2j + 1)^2)}, \qquad D_{\mathrm{tail}}^{(\mathrm{odd})}(t) := \frac{D_K^{(\mathrm{odd})}(t)}{D_N^{(\mathrm{odd})}(t)}.
\]
\item Because the character sign $\chi_{-4}(2j + 1) = (-1)^j$, the Vandermonde derivative sign $\operatorname{sgn}\big(D_{\mathrm{tail}}^{(\mathrm{odd})\prime}(-(2j + 1)^2)\big) = (-1)^{j - N}$, and the numerator sign $\operatorname{sgn}\big(D_N^{(\mathrm{odd})}(-(2j + 1)^2)^{2m-1}\big) = (-1)^N$ multiply to $(-1)^j (-1)^{j-N} (-1)^N = (-1)^{2j} = +1$, we have $\gamma_j^{(\beta(4))} > 0$ for every $N \le j < K$. Consequently, $M_K^{(\beta(4))}$ is strictly positive definite, and all $h$ roots of $\Delta_K^{(\beta(4))}(X)$ are unconditionally real.
\end{enumerate}
```

## Upstream paper items

- [2.5](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p02-05_construction/Experimental/P02_05/Target.md)
- [5.3](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-03_construction/Experimental/P05_03/Target.md)

## Imported facts and definitions

- `ManuscriptChain.PoleDiagonalization.lagrangeCoefficientMatrix_eq_inverse`
- `ManuscriptChain.DualSpectral.coefficientSlope_posDef`

## Explicit interface coverage

Explicit odd-square denominator and both printed differential-weight expressions are encoded. This is only the kernel and pole-algebra input layer; no calibrated one-variable β(4) rational functional has been supplied in the active repository.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

Normalization/sign review remains mandatory: the verbatim formulas are recorded as targets, not asserted by the experimental axioms. Existing positive-slope spectral results do not calibrate the β-functional.

Discharge derivative integrability and boundary terms; define the actual β series and one-variable rational functional; verify every normalization in the sech moment/partial-fraction formulas before calibration. Construct odd-pole Lagrange transport, signs and hyperbolicity from the actual functional. Do not assume the printed positive-weight identity.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
