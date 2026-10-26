# P04_04 — Sharpened spectral bound and effective irrationality measure for $\zeta(5)$

Status: **SOURCE_ONLY_UNCOMPILED**. Experimental prerequisites only. No Lean execution or target proof is represented.

## Exact original statement

```tex
\label{thm:zeta5-measure}
For all sufficiently large $K \in 30\ZZ_{>0}$, the relative matrix $B_K^{(5)} = G_K^{(5)}(\zeta(5))^{-1/2} M_K^{(5)} G_K^{(5)}(\zeta(5))^{-1/2}$ satisfies
\begin{equation}\label{eq:BK5-bound}
\|B_K^{(5)}\| \le e^{\rho_5^\star K}, \qquad \rho_5^\star := \frac{11411}{1000} = 11.411.
\end{equation}
Consequently, there exists an effectively computable positive integer $b_0$ such that for every $a \in \ZZ$ and every integer $b \ge b_0$,
\begin{equation}\label{eq:zeta5-measure}
\left|\zeta(5) - \frac{a}{b}\right| > b^{-25687}.
\end{equation}
```

## Imported verified facts

- `ManuscriptChain.Real.delta_eval_eq_det_gram`
- `ManuscriptChain.GRAM_POSITIVE`
- `ManuscriptChain.PoleDiagonalization.delta_natDegree`
- `ManuscriptChain.ACTUAL_OPERATOR_ZERO_FREE_DISK`
- `ManuscriptChain.Section4EffectiveBudget.manuscript_effective_rate_margins`

## Typed assumptions and coverage

The exact weight-five parameter lattice and printed S_K are defined, with separate arithmetic, energy and finite-polynomial analytic prerequisites. None assumes the theorem’s operator norm bound or rational approximation measure.

- `Experimental.P04_04.fauzan_multiplier_input`: Positive rational multiplier, coefficient integrality for the actual S_K Δ_K, and its separate upper logarithmic rate from cited Fauzan [5]. Does not assert the target spectral cap, decay of Q as a combined conclusion, or irrationality. Dependencies: EXTERNAL_FAUZAN_2026_PRIME_MULTIPLIER, P02_04.
- `Experimental.P04_04.fauzan_gram_energy_input`: Separate normalized actual Gram determinant upper rate 2.32380 attributed to Fauzan [5]. Dependencies: EXTERNAL_FAUZAN_2026_ENERGY, P03_01.
- `Experimental.P04_04.negative_node_polynomial_bound`: Classical finite-degree polynomial evaluation bound outside a positive interval in terms of its actual L² integral; supports the spectral argument only. Dependencies: EXTERNAL_DLMF_18_10_5_LEGENDRE.

## Repair, interface and discharge obligations

- Read and verify the actual Fauzan [5] source, including exact parameter family, multiplier prime exponents and effective cutoffs; the citation alone does not certify either axiom.
- The existential multiplier is not an implementation of m_{K,100000}=∏p^{-L_p}. Reconstruct that raw arithmetic object and its q-adic proof before claiming the explicit original normalization.
- Prove the finite polynomial bound from the correct Legendre normalization and actual integrals, then derive the Gram lower bound, exact residue factorial formula, uniform Stirling envelopes and certified scalar maximizer bound.
- Replace eventual source rates by explicit onsets/rational error budgets before claiming the effective b₀. Keep this experimental source outside the verified umbrella.

## Remaining work

Build the original explicit multiplier and transport the separate source estimates. Derive the spectral norm cap 11.411 for actualB; then combine a proved nonzero decay estimate, all-root separation and effective rate data. No such derivation is included here.

Each named axiom must be replaced by a proved declaration on these exact definitions and re-audited in the separately authorized execution target. A successful compile of an experimental axiom is not proof of its mathematical content.
