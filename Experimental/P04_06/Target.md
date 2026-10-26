# P04_06 — Two-sided determinant bounds and coefficient heights

Status: **SOURCE_ONLY_UNCOMPILED**. Experimental prerequisites only. No Lean execution or target proof is represented.

## Exact original statement

```tex
\label{thm:height-bounds}
For all sufficiently large $K \in 30\ZZ_{>0}$:
\begin{enumerate}
\item The determinant of $B_K^{(5)}$ satisfies the unconditional two-sided bounds
\begin{equation}\label{eq:det-BK-twosided}
0.23310 \le \liminf_{K\to\infty} \frac{1}{K^2} \log |\det B_K^{(5)}| \le \limsup_{K\to\infty} \frac{1}{K^2} \log |\det B_K^{(5)}| \le 3.73980.
\end{equation}
\item The normalized polynomial $Q_K^{(5)}(X) \in \ZZ[X]$ and primitive polynomial $P_K^{(5)}(X) \in \ZZ[X]$ satisfy
\begin{equation}\label{eq:height-QK-PK}
0.23\,K^2 \le \log H\big(Q_K^{(5)}\big) \le 10.27\,K^2, \qquad \log H\big(P_K^{(5)}\big) \le 10.27\,K^2,
\end{equation}
and the decay rate $\epsilon_P := \limsup_{K\to\infty} \big(-K^{-2} \log P_K^{(5)}(\zeta(5))\big)$ satisfies $0.0004 \le \epsilon_P \le 3.73980$. Moreover, writing $Q_K^{(5)}(X) = c_K P_K^{(5)}(X)$ with $c_K = \cont_\ZZ(Q_K^{(5)}) \in \ZZ_{>0}$ and $\delta_K := K^{-2} \log c_K \ge 0$, we have $\log H(P_K^{(5)}) \ge (0.23265 - \delta_K - o(1))K^2$ and $\log P_K^{(5)}(\zeta(5)) \le -(\epsilon + \delta_K)K^2$.
\end{enumerate}
```

## Imported verified facts

- `ManuscriptChain.PotentialGap.base_det_mul_whitened_det`
- `ManuscriptChain.PotentialGap.manuscript_normalized_log_identity`
- `ManuscriptChain.PotentialGap.evaluation_upper_gives_rate_lower`
- `ManuscriptChain.PotentialGap.evaluation_lower_gives_rate_upper`

## Typed assumptions and coverage

The finite determinant/log identities are already imported. Only independent classical arcsine probability/potential inputs for the Jensen lower bound are axiomatized; no target determinant rate, height bound or decay rate is assumed.

- `Experimental.P04_06.arcsine_probability_input`: Classical arcsine density is an integrable probability density on (0,L). Dependencies: CLASSICAL_ARCSINE_MEASURE.
- `Experimental.P04_06.arcsine_log_potential_input`: Actual logarithmic potential of that density at −u² with explicit closed value and integrability. Dependencies: CLASSICAL_ARCSINE_LOG_POTENTIAL.

## Repair, interface and discharge obligations

- Prove both classical identities and all needed Fubini/Jensen integrability conditions on the actual high-dimensional Andréief integrand.
- Construct the exact S_K normalizer and the original Q_K multiplier interface in this branch or import a discharged upstream implementation; a chosen primitive normalizer alone is insufficient.
- Establish actual Euler–Maclaurin and Gram-energy asymptotics with certified constants. Neither follows from finite log conservation.
- The printed lower coefficient-height argument reverses A_M≤−2.32425 into a lower bound. This is a REPAIR gate: obtain an independent valid lower multiplier-rate estimate or revise the claim. Do not assume the invalid inference.
- Full paper polynomial-height and limsup statements remain unproved; source-only axioms do not close them.

## Remaining work

Connect the actual determinant to the restricted Andréief integral, justify Jensen/Fubini and derive each asymptotic bound separately. Repair the coefficient-height lower estimate before attempting the full original item.

Each named axiom must be replaced by a proved declaration on these exact definitions and re-audited in the separately authorized execution target. A successful compile of an experimental axiom is not proof of its mathematical content.
