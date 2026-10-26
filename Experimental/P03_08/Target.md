# Experimental paper item 3.8: Christoffel--Darboux pole representation and Jacobi derivative identity

Status: **SOURCE_ONLY_UNCOMPILED**. This branch is a typed experimental boundary, not a proof certificate. No Lean execution was performed. Existing proof facts retain their original source receipts; the new files have no compile/audit receipt.

## Original statement (verbatim source TeX)

PDF page 12; source label `thm:CD-kernel`. The following text is copied without correction from `manuscript_complete_inventory.json`.

```tex
\label{thm:CD-kernel}
Let $\{\pi_r(t)\}_{r=0}^{h-1}$ be the monic orthogonal polynomials on $[0, \infty)$ with respect to $d\mu_\xi(t) := \frac{D_N(t)^{2m}}{D_K(t)} \frac{w_s(\sqrt{t})}{2\sqrt{t}}\,dt$, and let
\[
\mathcal{K}_h(t, u) := \sum_{r=0}^{h-1} \frac{\pi_r(t) \pi_r(u)}{\int_0^\infty \pi_r(v)^2\,d\mu_\xi(v)} = (1, t, \dots, t^{h-1}) G_K^{(s)}(\xi)^{-1} (1, u, \dots, u^{h-1})^T
\]
be their Christoffel--Darboux kernel.
\begin{enumerate}
\item The non-zero eigenvalues $\beta_1, \dots, \beta_h$ of $B_K^{(s)}$ coincide with the eigenvalues of the $h \times h$ pole-kernel matrix $\big[ \gamma_a^{(s)} \, \mathcal{K}_h(-a^2, -b^2) \big]_{N < a,b \le K}$.
\item Under the Laplace scaling $w_s(y; \tau) := \frac{2(2\pi)^{2k}}{(2k)!} y^{2k+1} \sum_{l=1}^\infty l^{2k} e^{-2\pi l \tau y}$ ($\tau > 0$) applied to the weight, with the evaluation point $\xi = \zeta(s)$ held fixed, the deformed determinant $\Delta_K\big(\xi; \tau\big) := \det G_K^{(s)}\big(\xi; \tau\big)$ satisfies
\begin{equation}\label{eq:Jacobi-CD}
\frac{\partial}{\partial \tau} \log \Delta_K\big(\xi; \tau\big) = \int_0^\infty \mathcal{K}_h(y^2, y^2; \tau) \frac{D_N(y^2)^{2m}}{D_K(y^2)} \frac{\partial w_s(y; \tau)}{\partial \tau}\,dy,
\end{equation}
where the partial derivative $\partial/\partial\tau$ is taken with $X = \xi$ fixed.
\end{enumerate}
```

## Prerequisites and direction

- `Experimental.P03_08.laplace_density_hasDerivAt`: For every natural k and positive tau,y, the displayed infinite exponential density has the displayed termwise tau derivative.
  - Upstream dependencies: Explicit laplaceTerm/density/densityDerivative definitions; Termwise parameter differentiation and convergence of the actual exponential series.
  - Direction: 3.8(2) moment differentiation, not the determinant/Jacobi target.
- `Experimental.P03_08.laplace_moment_local_domination`: For every actual admissible tuple p, every moment order e and positive tau0, an epsilon<tau0 and one integrable majorant dominate the actual moment and its proposed derivative uniformly on that neighborhood.
  - Upstream dependencies: Definition 2.1 denominator polynomials and actual p; Exponential-tail estimates, rational-weight polynomial growth, local integrability at zero.
  - Direction: 3.8(2) dominated parameter integration; no determinant formula is an assumption.

## Existing upstream facts

- `Experimental.P03_08.base_gram_positive` aliases `ManuscriptChain.GRAM_POSITIVE` (paper dependency 3.1 / odd-weight moment realization).

## Formula coverage and missing interfaces

The exact displayed Laplace series and actual D_N(y^2)^(2m)/D_K(y^2) rational weight are defined. The two new inputs support parameter differentiation of moments only. The determinant derivative and CD spectral identity remain targets.

The definition uses the paper's odd-weight Laplace normalization, with the zeta evaluation point to remain fixed. No existing unimported ChristoffelDarboux or LaplaceJacobiIdentity candidate is imported. Missing interfaces: tau=1 density identification, measurability, deformed moment measure/Gram, actual monic orthogonal polynomials and integral squared norms, CD inverse-Gram identification, pole operator, characteristic polynomial comparison, and matrix logarithmic derivative assembly. The two analytic inputs deliberately support only part (2); part (1) starts from the imported actual positive Gram and algebraic slope facts.

## Integration and discharge obligations

1. Publish the files under `Experimental/P03_08/`; `Work.lean` imports only its named prerequisites, which import the existing active verified root `Zetahyperbolic`.
2. Elaborate this exact source in the authorized target with pinned Lean/Mathlib. Until that happens, even declaration syntax is unverified. Do not treat the old root CI receipt as evidence for these new modules.
3. Keep every new axiom named in `Assumptions.json` in the transitive audit report. Prove each exact quantified input before promotion; do not weaken the target, change the actual objects, or silently add new premises.
4. Record separately which original clauses are obtained and which remain open. Any corrected formulation must be separately named and must not replace the literal statement above.
5. A target proof using these inputs is an experimental conditional result. Only an exact discharged proof and successful source-bound compilation/axiom audit can change its status. This scaffold declares no target theorem and contains no placeholder proof.
