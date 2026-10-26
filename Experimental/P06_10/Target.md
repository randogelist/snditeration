# Theorem 6.10: Universal potential-gap identity and vanishing of quadratic derivative growth in two variables

Status: **SOURCE_ONLY_UNCOMPILED**. This cell is an experimental prerequisite scaffold, not a verified theorem. No compilation or axiom audit has been run.

## Original statement (verbatim TeX)

```tex
\label{thm:potential-gap-2v}
\begin{enumerate}
\item \emph{(Potential-gap conservation law for one-variable Hankel pencils)} Let $G_K^{(s)}(X) = G_K^{(s)}(\zeta(s)) + (X - \zeta(s)) M_K^{(s)}$ be a one-variable Hankel pencil of degree $h = \lambda K$ built from a rational kernel $W_K(t) / D_K(t)$ with simple poles at $v_a = -a^2$ ($N < a \le K$) and positive weight $W_K(t) > 0$ on $(0, \infty)$, normalized by $m_K S_K > 0$ so that $Q_K(X) := m_K S_K \det G_K^{(s)}(X) \in \mathbb{Z}[X]$ has decay rate $\epsilon := \lim_{K \to \infty} (-K^{-2}\log Q_K(\zeta(s))) > 0$. Then the leading-coefficient height rate $\Lambda_{\mathrm{lead}} := \lim_{K \to \infty} K^{-2}\log|[X^h] Q_K(X)| \le \Lambda_{\mathrm{height}}$ satisfies the exact identity
\[
\Lambda_{\mathrm{lead}} + \epsilon = \mathcal{I}_B := \lim_{K \to \infty} \frac{1}{K^2}\log|\det B_K^{(s)}| = \mathcal{E}(\mu_{\mathrm{eq}}) - \mathcal{E}_{\mathrm{poles}}(\nu_{\mathrm{unif}}),
\]
where $\mathcal{E}(\mu_{\mathrm{eq}})$ is the minimum weighted logarithmic energy on $[0, \infty)$ and $\mathcal{E}_{\mathrm{poles}}(\nu_{\mathrm{unif}})$ is the logarithmic energy on the negative pole lattice. Moreover, multiplying $W_K(t)$ by $P_K(t)^2$ for any polynomial family $P_K(t)$ with positive real roots and empirical measure $\sigma_P$ on $[0, \alpha^2]$ satisfies $\mathcal{I}_B(P_K) \ge \mathcal{I}_B(1) + 2\lambda\big(\int_\alpha^1 U^{\sigma_P}(-u^2)\,\frac{du}{\lambda} - \int U^{\sigma_P}(t)\,d\mu_{\mathrm{eq}}(t)\big) > \mathcal{I}_B(1)$, and any integer multiple $\widetilde{Q}_K(X) = c_K P_K^{(5)}(X) \in \mathbb{Z}[X]$ ($c_K \in \mathbb{Z}_{>0}$) satisfies $\widetilde{\Lambda}_{\mathrm{height}} + \tilde{\epsilon} \ge \mathcal{I}_B^{(5)} \ge 0.23310$, whence $\widetilde{\Lambda}_{\mathrm{height}} / \tilde{\epsilon} > 581 > 1$.
\item \emph{(Vanishing of quadratic derivative-determinant growth in the two-variable Beukers architecture)} For any odd integer $s = 2k + 1 \ge 3$, define the two-variable Beukers measure $d\Omega_s(x_1, x_2) := \frac{1}{(2k)!}\frac{(-\log(x_1 x_2))^{2k-1}}{1 - x_1 x_2}\,dx_1\,dx_2$ on $(0, 1)^2$. Let $h = \lfloor \lambda K \rfloor$ ($\lambda \in (0, 1)$), and let $\mathcal{A}_K = \{A_0(x), \dots, A_{h-1}(x)\} \subset \mathbb{Z}[x]_{\le K}$ be any sequence of $h$ linearly independent integer polynomials whose coefficient matrix $C_K \in M_{h \times (K+1)}(\mathbb{Z})$ has polynomially bounded height $\max_{i, r} |C_{i, r}| \le K^A$ ($A \ge 0$ fixed). Then the $X$-derivative determinant $M_{\mathcal{A}_K}^{(s)} = [X] G_{\mathcal{A}_K}^{(s)}(X) = C_K C_K^T$ satisfies
\[
1 \le \det M_{\mathcal{A}_K}^{(s)} = \det(C_K C_K^T) \le (K + 1)^h K^{2 A h},
\]
and hence its quadratic exponential growth rate vanishes identically:
\[
\lim_{K \to \infty} \frac{1}{K^2}\log \det M_{\mathcal{A}_K}^{(s)} = \lim_{K \to \infty} \frac{1}{K^2}\log \det(C_K C_K^T) = 0.
\]
\end{enumerate}
```

## Dependency direction

Earlier inputs → this theorem: 2.5, 3.1, 4.6, 5.2. Dependencies come from the statement and proof; they do not authorize replacing this theorem by its own conclusion as an assumption. Existing declarations below are reused by import/export. Proposed earlier beta identities are explicitly axiomatized only where listed.

## Reused current declarations

- `ManuscriptChain.PotentialGap.manuscript_normalized_log_identity`
- `ManuscriptChain.PotentialGap.height_decay_ratio_gt_581`
- `ManuscriptChain.PotentialGap.lower_decay_bound_counterexample`
- `ManuscriptChain.CoefficientGramGrowth.normalized_log_det_tendsto_zero`

## Typed prerequisite coverage

Concrete admissible-family parameters, positive normalization data, and integral coefficient matrices with row independence and polynomial entry bounds. Existing finite logarithmic conservation and coefficient-Gram growth declarations are imported, not assumed anew.

## Explicit assumptions

No new axioms. The useful current interface consists of concrete data and imported results; missing analytic/arithmetic infrastructure is left open.

## Missing domain interfaces

Weighted equilibrium measures, logarithmic-energy domains, the existence and identification of potential limits, strict reweighting inequality and an explicit upper decay estimate are not encoded.

## Repair and discharge gates

- The printed >581 deduction cannot use only a lower decay bound. Preserve the existing counterexample and require the corrected upper-decay condition or change the conclusion.
- Do not replace a positive limiting potential gap by the finite identity.
- The imported growth theorem uses a weaker factorial upper bound; do not label it as the literal finite Hadamard bound.

- Replace every explicit upstream axiom with its corresponding checked theorem before promoting any result that depends on it.
- Compile this module and audit the exact final declaration on the authorized target. Source-only status never implies a PASS.
- Preserve the exact original statement above for comparison; any repair needs a distinct accurately stated conclusion and must not inherit the original status automatically.
