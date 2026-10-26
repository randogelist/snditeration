# Proposition 5.3 — Two-variable Beukers measure and dual pencil for $\beta(4) = L(4, \chi_{-4})$

Status: **SOURCE_ONLY_UNCOMPILED**. This is an experimental prerequisite scaffold, not a proof certificate. No Lean/build execution was performed.

## Exact original statement

```tex
\label{prop:beta4-pencil}
Define the positive measure $d\Omega_{\beta(4)}(x_1, x_2) := \frac{1}{6} \frac{(-\log(x_1 x_2))^2}{1 + x_1^2 x_2^2}\,dx_1\,dx_2 > 0$ on $(0, 1)^2$, and let $H_m^{(\beta, s)} := \sum_{n=0}^{m-1} \frac{(-1)^n}{(2n+1)^s}$ ($H_0^{(\beta, s)} := 0$). Then for all integers $k_1, k_2 \ge 0$:
\[
\iint_{(0, 1)^2} x_1^{4 k_1} x_2^{4 k_2} \, d\Omega_{\beta(4)}(x_1, x_2) = \begin{cases} \beta(4) - H_{2k}^{( \beta, 4)}, & \text{if } k_1 = k_2 = k, \\[8pt] \dfrac{1}{12} \dfrac{H_{2k_1}^{(\beta, 3)} - H_{2k_2}^{(\beta, 3)}}{k_1 - k_2} \in \QQ, & \text{if } k_1 \neq k_2. \end{cases}
\]
Consequently, for any linearly independent subspace $\mathcal{A} \subset \QQ[x^4]_{\le 4K}$ of dimension $h$, the induced symmetric matrix pencil $G_{\mathcal{A}}^{(\beta(4))}(X)$ has positive definite $X$-derivative $C C^T \succ 0$ and all $h$ roots of $\det G_{\mathcal{A}}^{(\beta(4))}(X)$ are real.
```

## Imported verified source boundary

`Zetahyperbolic` at `randogelist/snditeration@3b184ba109f065d973957a5735fb590fea4b0e35`; Lean 4.33.0 and pinned Mathlib. Existing proved components are imported, not re-axiomatized. Current source/audit and historical target-specific receipts govern those imports; this experimental extension has not compiled.

## Typed prerequisite coverage

Concrete printed beta4 density and mode definitions plus one convergence prerequisite; no moment identity or beta hyperbolicity conclusion assumed.

- `Experimental.P05_03.betaFour_modes_integral_norm_summable`: Absolute summability of the integrals of the actual alternating geometric mode norms for every pair of monomial indices.

## Remaining object-interface and proof work

Prove each mode is integrable using existing arbitrary-order Mellin logarithmic integrals; identify pointwise geometric expansion; justify integral/tsum interchange; construct and identify the actual beta series and rational harmonic tails; only then transport the true coefficient pencil to finite positive-slope spectrum.

## Repair gate

Do not treat pointwise positive density as positivity of the bilinear coefficient form. Preserve the printed normalization and audit it against exact low-index moments before accepting any target conclusion.

## Discharge obligations

Replace summability axiom by exact Mellin term estimates and a convergent numerical majorant. The series-to-beta moment identity and all finite-pencil identifications remain separate work.

## Dependency identifiers

`P05_01_UNIT_LOG_MOMENTS`, `P05_02_FINITE_SPECTRUM`.
