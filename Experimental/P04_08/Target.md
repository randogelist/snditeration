# P04_08 — Rational root exclusion and degree bounds for cluster factors

Status: **SOURCE_ONLY_UNCOMPILED**. Experimental prerequisites only. No Lean execution or target proof is represented.

## Exact original statement

```tex
\label{prop:factor-degree}
Let $K \in 30\ZZ_{>0}$ be sufficiently large, and let $F(X) = c_F \prod_{m=1}^d (X - r_{j_m}) \in \ZZ[X]$ ($c_F \in \ZZ \setminus \{0\}$) be a non-constant divisor of $P_K^{(5)}(X)$.
\begin{enumerate}
\item No rational number $a/b \in \QQ$ with denominator $1 \le b \le \exp(K / 2251)$ is a root of $P_K^{(5)}(X)$, and any rational root $a/b$ of $P_K^{(5)}(X)$ lying in $|X - \zeta(5)| \le e^{-\tau K}$ ($\tau > 0$) satisfies $b \ge \exp\!\big(\frac{\tau}{25687} K\big)$.
\item The degree $d = \deg F$ satisfies the unconditional lower bound
\begin{equation}\label{eq:factor-deg-lower}
\deg F = d \ge \frac{\log|c_F| - \log|F(\zeta(5))|}{\rho_5^\star K} \ge \frac{-\log|F(\zeta(5))|}{11.411 K},
\end{equation}
and if all roots of $F(X)$ lie in the cluster disk $|r_{j_m} - \zeta(5)| \le e^{-\tau K}$ ($\tau > 0$), then $d$ also satisfies the upper bound $d \le \frac{\log|c_F| - \log|F(\zeta(5))|}{\tau K}$.
\end{enumerate}
```

## Imported verified facts

- `ManuscriptChain.primitivePolynomial_root_iff`
- `ManuscriptChain.Spectral.actual_complex_root_distance`
- `ManuscriptChain.primitivePolynomial_isPrimitive`
- `ManuscriptChain.primitivePolynomial_natDegree`

## Typed assumptions and coverage

Only genuine earlier Theorem 4.4 inputs are exposed. These can support factor-distance bounds and the denominator bound for a rational root already known to be clustered. The blanket small-denominator exclusion remains behind a repair gate.

- `Experimental.P04_08.weight_five_spectral_cap_input`: Earlier 4.4 actual operator-norm cap, which gives a lower root-distance gap after proved transfer, not an upper cluster radius. Dependencies: P04_04_SPECTRAL.
- `Experimental.P04_08.zeta_five_measure_input`: Earlier 4.4 rational approximation bound after an existential threshold, on the actual real zeta series. Dependencies: P04_04_MEASURE.

## Repair, interface and discharge obligations

- Discharge both earlier 4.4 inputs. Their assumptions are experimental, not existing certified zeta estimates.
- The paper turns |r−ζ5|≥exp(−11.411K) into |r−ζ5|≤exp(−11.411K). Never introduce that upper-cluster statement as an axiom or use ex-falso to cross this gap.
- Part (1) unconditional small-denominator exclusion requires an independent new argument or a corrected statement. The conditional clustered-root assertion has a different scope.
- Part (2) printed upper degree inequality should be checked carefully: from |F(ξ)|≤|c_F|exp(−dτK), logarithms give d≤(log|c_F|−log|F(ξ)|)/(τK). Keep all positivity/nonzero conditions explicit.
- Represent actual polynomial divisors, complex root multiplicities and leading coefficients; prove finite factor-product/log inequalities instead of assuming the target degree bounds.

## Remaining work

Develop factor evaluation products for actual divisors and prove the conditional clustered-root denominator bound from the upstream measure. Stop at the explicitly recorded global-exclusion repair gate; no false upper-cluster premise is admitted.

Each named axiom must be replaced by a proved declaration on these exact definitions and re-audited in the separately authorized execution target. A successful compile of an experimental axiom is not proof of its mathematical content.
