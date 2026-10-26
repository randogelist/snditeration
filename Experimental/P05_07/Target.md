# Theorem 5.7 — Simultaneous double-pole Hankel determinant for $\{1, \zeta(5), \zeta(6)\}$

Status: **SOURCE_ONLY_UNCOMPILED**. This is an experimental prerequisite scaffold, not a proof certificate. No Lean/build execution was performed.

## Exact original statement

```tex
\label{thm:double-pole}
Suppose $a \zeta(5) + b \zeta(6) = c$ with $a, b, c \in \ZZ$ and $b \neq 0$. For $n \ge 1$, define the rational function
\begin{equation}\label{eq:Rn-double}
R_n(t) := \frac{((6n)!)^2 \prod_{j=1}^{n} (t - j + 1)^5}{\prod_{k=0}^{6n} (t + k)^2}.
\end{equation}
For every polynomial $P(t) \in \QQ[t]$ with $\deg P < 6n$, $\deg(R_n(t) P(t)) \le -n - 3 \le -4$ has zero polynomial part and zero residue at $t = \infty$, and its partial fraction decomposition defines the rational linear functional
\begin{equation}\label{eq:Ln-double}
\mathcal{L}_n(P) := \frac{1}{n!} \sum_{k=0}^{6n} \Big[ A_{n, k} \big(U_k P'(-k) + V_k P(-k)\big) + B_{n, k} U_k P(-k) \Big] \in \QQ,
\end{equation}
where $A_{n, k} = (-1)^k \binom{6n}{k}^2 \binom{n+k}{k}^5 n!$, $B_{n, k} = A_{n, k}(7 H_k^{(1)} - 2 H_{6n-k}^{(1)} - 5 H_{n+k}^{(1)})$, $U_k = c - a H_k^{(5)} - b H_k^{(6)}$, and $V_k = \frac{a}{k^6} + \frac{b}{5k^7}$ ($V_0 = 0$). Let $J_n := \det_{0 \le i,j < 3n} [\mathcal{L}_n(t^{i+j})] \in \QQ$. Then:
\begin{enumerate}
\item For every prime $q > \max(|b|, 11)$ satisfying $q \equiv 1 \pmod 9$, set $m = (q - 1)/9$ and $n = 2m$. Then $v_q(J_{2m}) = -18n = -36m < 0$; in particular, $J_{2m} \neq 0$.
\item For every prime $p \in (\sqrt{6n}, 6n]$, let $L_\rho := \#\{0 \le k \le 6n : k \equiv \rho \pmod p\}$ and $\omega_p(\rho) := 2\lfloor \frac{6n}{p}\rfloor - 2\lfloor \frac{6n-\rho}{p}\rfloor + 5\lfloor \frac{n+\rho}{p}\rfloor - 5\lfloor \frac{n}{p}\rfloor \ge 0$. Then
\begin{equation}\label{eq:vp-Jn-bound}
v_p(J_n) \ge \min_{\substack{0 \le m_\rho \le 2 L_\rho \\ \sum_{\rho=0}^{p-1} m_\rho = 3n}} \sum_{\rho=0}^{p-1} m_\rho\big(m_\rho - 1 + \omega_p(\rho) - 7\big).
\end{equation}
\end{enumerate}
```

## Imported verified source boundary

`Zetahyperbolic` at `randogelist/snditeration@3b184ba109f065d973957a5735fb590fea4b0e35`; Lean 4.33.0 and pinned Mathlib. Existing proved components are imported, not re-axiomatized. Current source/audit and historical target-specific receipts govern those imports; this experimental extension has not compiled.

## Typed prerequisite coverage

Object-interface scaffold only: actual rational function and literal displayed A/B/U/V, functional and determinant definitions. No axiom is safe or necessary before the coefficient table has been matched to the rational function.

No axioms are introduced at this stage.

## Remaining object-interface and proof work

Construct actual order-two residue coefficients; verify degree/zero-polynomial-part assertions and table identity, including k=0; define q-adic valuations with zero conventions; construct confluent/Hermite bases and local blocks; prove exact determinant valuations and minor bounds. The assumed integer relation aζ5+bζ6=c must remain explicit in any eventual conditional theorem.

## Repair gate

Do not axiomatize the displayed A/B table as the actual residue table without checking it. Equation (5.8) has numerator factors indexed j=1,…,n and denominator nodes including k=0; endpoint normalization and indexing are an explicit gate. No claimed inconsistency is used as an axiom or ex-falso route. 5.4 is simple-pole only and provides no automatic higher-order extension.

## Discharge obligations

No axioms currently admitted. First produce a consistent verified object identification; only then consider named, independently justified local valuation prerequisites. Never assume the final -36m determinant valuation as a prerequisite.

## Dependency identifiers

`P05_05_SIMPLE_POLE_SCOPE`, `DOUBLE_POLE_RESIDUE_INTERFACE`.
