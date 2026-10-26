# Experimental paper item 3.9: Hyperbolicity for Hurwitz and Dirichlet Hankel determinants

Status: **SOURCE_ONLY_UNCOMPILED**. This branch is a typed experimental boundary, not a proof certificate. No Lean execution was performed. Existing proof facts retain their original source receipts; the new files have no compile/audit receipt.

## Original statement (verbatim source TeX)

PDF page 13; source label `thm:hurwitz-dirichlet`. The following text is copied without correction from `manuscript_complete_inventory.json`.

```tex
\label{thm:hurwitz-dirichlet}
\begin{enumerate}
\item Let $\theta \in (0, 1] \cap \QQ$ and $s = 2k+1 \ge 3$. Set $D_{m, \theta}(t) := \prod_{j=0}^{m-1} (t + (j + \theta)^2)$, and let $\mu_{X, \theta}^{(s)}$ be the rational functional on simple poles at $t = -(j + \theta)^2$ defined via Hermite's integral formula at $X = \zeta(s, \theta)$:
\[
\int_0^\infty \frac{w_s(y)}{y^2 + (j + \theta)^2}\,dy = (j + \theta)^{2k}\left(\zeta(s, \theta) - \sum_{\nu=0}^{j-1} \frac{1}{(\nu + \theta)^s}\right) + r_{j, \theta} \qquad (r_{j, \theta} \in \QQ).
\]
Then $\Delta_{K, \theta}^{(s)}(X) := \det\big[\mu_{X, \theta}^{(s)}(D_{N, \theta}(t)^{2m} t^{i+j} / D_{K, \theta}(t))\big]_{0 \le i,j < h}$ has exact degree $h$ and all its roots are real.
\item Let $\chi \pmod q$ be a primitive real Dirichlet character of conductor $q \in \{3, 4, 5, 8\}$, and choose $a_0 \in \{1, \dots, q-1\}$ with $\chi(a_0) = +1$. Set $j_r := q r + a_0$ ($r \ge 0$) and $D_{m, \chi}(t) := \prod_{r=0}^{m-1} (t + j_r^2)$. Then the Dirichlet generating kernel $g_\chi(y) := \sum_{l=1}^\infty \chi(l) e^{-2\pi l y / q}$ is strictly positive for all $y > 0$. For any integer $s \ge 2$, let $\Omega_{s, \chi}(y) := y^{s-1} g_\chi(y) > 0$, and let $\mu_{X, \chi}^{(s)}$ be the linear functional defined on $t^e$ by $\int_0^\infty y^{2e} \Omega_{s, \chi}(y)\,dy$ and on simple poles $(t + j_r^2)^{-1}$ by $j_r^{s-1}(X - \xi_\chi) + \int_0^\infty \frac{\Omega_{s, \chi}(y)}{y^2 + j_r^2}\,dy$ (where $\xi_\chi := L(s, \chi)$ when $\chi(-1) = (-1)^{s-1}$). Then $\Delta_{K, \chi}^{(s)}(X) := \det\big[\mu_{X, \chi}^{(s)}(D_{N, \chi}(t)^{2m} t^{i+j} / D_{K, \chi}(t))\big]_{0 \le i,j < h}$ has exact degree $h$ and all its roots are real.
\end{enumerate}
```

## Prerequisites and direction

- `Experimental.P03_09.hurwitz_pole_integral_rational_remainder`: For every k>0, rational 0<theta<=1 and j>=0, the actual density divided by y^2+(j+theta)^2 is integrable and its integral differs from the actual shifted Hurwitz tail times (j+theta)^(2k) by a rational number.
  - Upstream dependencies: Imported odd-weight Hyperbolic.density; Shifted Hurwitz Dirichlet series and finite initial sum; Rational-shift Hermite pole identity.
  - Direction: Rational shifted-pole moment functional used upstream of 3.9(1) hyperbolicity.
- `Experimental.P03_09.character_power_series_blocks`: For each of the five explicit primitive-real-character coefficient tables and every 0<z<1, the power series HasSum equals its displayed factored numerator divided by 1-z^q.
  - Upstream dependencies: Explicit periodic coefficient tables for conductors 3,4,5,8; Geometric-series regrouping and absolute convergence.
  - Direction: 3.9(2) character kernel analysis; positivity is to be proved, not an axiom.

## Existing upstream facts

No new theorem alias is needed for the scalar inputs; the existing verified project is imported.

## Formula coverage and missing interfaces

Actual Hyperbolic.density pole integrals at rational shifted squares and actual shifted series are used. Five explicit coefficient tables and their factored numerators represent the requested real characters. Inputs are scalar pole-remainder and HasSum identities only.

No arbitrary character/pencil model is substituted for the paper: coefficient functions are explicit for chi_-3, chi_-4, chi_5, chi_8, chi_-8. Missing interfaces remain explicit: identification and exhaustion of Mathlib primitive real Dirichlet characters, exponential substitution for the defined characterKernel, character L-value centers and parity, identification of the shifted series with the standard Hurwitz function, actual simple-pole rational domains, numerator/denominator identities and moment integrability for all orders, positive moment measure, Vandermonde factorization and determinant degree/real-root transfer. Do not claim this scaffold covers those interfaces or all original quantifiers yet.

## Integration and discharge obligations

1. Publish the files under `Experimental/P03_09/`; `Work.lean` imports only its named prerequisites, which import the existing active verified root `Zetahyperbolic`.
2. Elaborate this exact source in the authorized target with pinned Lean/Mathlib. Until that happens, even declaration syntax is unverified. Do not treat the old root CI receipt as evidence for these new modules.
3. Keep every new axiom named in `Assumptions.json` in the transitive audit report. Prove each exact quantified input before promotion; do not weaken the target, change the actual objects, or silently add new premises.
4. Record separately which original clauses are obtained and which remain open. Any corrected formulation must be separately named and must not replace the literal statement above.
5. A target proof using these inputs is an experimental conditional result. Only an exact discharged proof and successful source-bound compilation/axiom audit can change its status. This scaffold declares no target theorem and contains no placeholder proof.
