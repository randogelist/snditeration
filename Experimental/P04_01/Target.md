# P04_01 — Spectral irrationality measure criterion

Status: **SOURCE_ONLY_UNCOMPILED**. Experimental prerequisites only. No Lean execution or target proof is represented.

## Exact original statement

```tex
\label{thm:spectral-criterion}
Let $\xi \in \RR$, let $d_0 \in \ZZ_{>0}$ and $\lambda, \epsilon, \rho > 0$, and suppose $\{Q_K(X)\}_{K \in d_0 \ZZ_{>0}} \subset \ZZ[X]$ is a sequence of integer polynomials of degree $d_K \le \lambda K$ whose complex roots $r_{K, 1}, \dots, r_{K, d_K} \in \CC$ satisfy, for all sufficiently large $K$:
\begin{enumerate}
\item $0 < |Q_K(\xi)| \le e^{-\epsilon K^2}$, and
\item $|r_{K, j} - \xi| \ge e^{-\rho K}$ for all $1 \le j \le d_K$.
\end{enumerate}
Then for every $\mu > \mu^* := \frac{\lambda \rho}{\epsilon}$, there exists an effectively computable integer $b_0(\mu)$ such that
\begin{equation}\label{eq:general-measure}
\left|\xi - \frac{a}{b}\right| > b^{-\mu}
\end{equation}
for all $a \in \ZZ$ and all integers $b \ge b_0(\mu)$.
```

## Imported verified facts

- `ManuscriptChain.Section4TransferComplete.spectral_transfer_lattice`
- `ManuscriptChain.Section4EffectiveBudget.effective_spectral_measure`
- `ManuscriptChain.Section4EffectiveBudget.denominatorThreshold`

## Typed assumptions and coverage

The already proved conditional transfer and integer-exponent effective API are imported. The record exposes the known-onset/rational-rate input required by that API, and does not invent an algorithm extracting it from arbitrary eventual estimates.

No axioms are introduced. The existing verified API is imported, and missing effective data is exposed as an input interface rather than asserted to exist.

## Repair, interface and discharge obligations

- The original real-exponent statement contains effectively computable b₀ without effective representations/onsets. Do not add an axiom claiming arbitrary eventual bounds have a computable onset.
- Keep the printed statement and the effective-data repair separate. The current effective imported API has a natural exponent; the paper quantifies over every real μ above its threshold.
- To connect a concrete family, construct its explicit onset and rational margins, then use the imported theorem. A record with proof fields is an assumption interface, not a finite raw-data witness checker.

## Remaining work

Connect supplied effective data to the imported theorem. Resolve representation/effectivity and real-exponent scope before claiming the full original statement. Do not infer any concrete ζ-family estimates.

Each named axiom must be replaced by a proved declaration on these exact definitions and re-audited in the separately authorized execution target. A successful compile of an experimental axiom is not proof of its mathematical content.
