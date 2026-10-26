# P04_05 — Irrationality and effective measure for $b\zeta(5) + a\zeta(3)$

Status: **SOURCE_ONLY_UNCOMPILED**. Experimental prerequisites only. No Lean execution or target proof is represented.

## Exact original statement

```tex
\label{thm:zeta5-zeta3-comb}
Let $a, b \in \ZZ$ be integers satisfying $b > 0$ and $a < \frac{\pi^2}{3} b \approx 3.2898 b$. Then the real number $\xi_{a,b} := b\zeta(5) + a\zeta(3)$ is irrational, and there exists an effectively computable integer $q_0(a, b)$ such that for all $p \in \ZZ$ and all integers $q \ge q_0(a, b)$,
\begin{equation}\label{eq:zeta5-zeta3-measure}
\left| b\zeta(5) + a\zeta(3) - \frac{p}{q} \right| > q^{-25687}.
\end{equation}
```

## Imported verified facts

- `ManuscriptChain.Hyperbolic.density`
- `ManuscriptChain.Hyperbolic.summable_exponentialTerm`
- `ManuscriptChain.Hyperbolic.density_pos`
- `ManuscriptChain.Mu.integral_rational_density`
- `ManuscriptChain.Section4TransferComplete.spectral_transfer_lattice`

## Typed assumptions and coverage

Only the genuine coupled-density comparison is assumed. Existing pure-weight analytic realization and rational moment facts remain imported. No ζ5/ζ3 irrationality, multiplier, decay or combined spectral statement is assumed.

- `Experimental.P04_05.coupled_density_comparison`: Pointwise comparison of actual w5 and b w5−a y²w3, with the manuscript coefficients and positive lower comparison. Only the analytic density prerequisite. Dependencies: P03_01, P04_05_ANALYTIC_COMPARISON.

## Repair, interface and discharge obligations

- Discharge comparison by the actual summable exponential series, retaining both signs of a.
- Construct the actual single-Z coupled rational pencil and prove slope equality and positive Gram realization. These objects are not replaced by a generic arbitrary matrix.
- Prove outer-prime rank-loss and small-prime bounds independently. The manuscript’s claimed rank ≤14 requires a separate actual matrix-rank proof.
- Track O(K) and O(log K) losses with sufficient strict rate margins; an O(log K) error cannot be silently discarded at the exact 11.411 bound.

## Remaining work

Construct and identify the mixed pencil, integrate the density comparison, discharge p-adic multiplier losses and effective decay, then invoke the imported transfer. This scaffold covers only the first analytic input.

Each named axiom must be replaced by a proved declaration on these exact definitions and re-audited in the separately authorized execution target. A successful compile of an experimental axiom is not proof of its mathematical content.
