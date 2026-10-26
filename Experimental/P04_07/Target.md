# P04_07 — Macroscopic exponential root collapse and root separation

Status: **SOURCE_ONLY_UNCOMPILED**. Experimental prerequisites only. No Lean execution or target proof is represented.

## Exact original statement

```tex
\label{thm:root-collapse}
For all sufficiently large $K \in 30\ZZ_{>0}$:
\begin{enumerate}
\item At least $N_{\mathrm{clust}} \ge 0.0140 h > \frac{12}{1000} K$ real roots $r_j$ of $P_K^{(5)}(X)$ satisfy
\begin{equation}\label{eq:macroscopic-collapse}
\big|r_j - \zeta(5)\big| \le e^{-0.10 K},
\end{equation}
while the closest root satisfies $e^{-11.411 K} \le \min_{1 \le j \le h} |r_j - \zeta(5)| \le e^{-K / 2250}$, and the arithmetic mean of the roots satisfies $\frac{1}{h}\sum_{j=1}^h r_j - \zeta(5) = -\frac{1}{h}\Tr\big((M_K^{(5)})^{-1} G_K^{(5)}(\zeta(5))\big)$.
\item Any two roots $r_- < \zeta(5) < r_+$ of $P_K^{(5)}(X)$ straddling $\zeta(5)$ satisfy $r_+ - r_- \ge 2 e^{-11.411 K}$, and any two roots $r_{i_a} \neq r_{i_b}$ belonging to the same irreducible factor $f(X) \mid P_K^{(5)}(X)$ in $\ZZ[X]$ of degree $d = \deg f \ge 2$ satisfy $|r_{i_a} - r_{i_b}| \ge \exp(-10.27 d K^2 - O(K\log K))$.
\end{enumerate}
```

## Imported verified facts

- `ManuscriptChain.Spectral.actual_complex_root_iff`
- `ManuscriptChain.Spectral.actual_complex_root_distance`
- `ManuscriptChain.primitivePolynomial_root_iff`
- `ManuscriptChain.ACTUAL_SPECTRAL_FACTORIZATION`

## Typed assumptions and coverage

Genuine earlier-item quantitative inputs are explicit on the actual family. The generic factor-height prerequisite covers one arithmetic step only. The final root-count, nearest-root, trace and separation claims are not assumed.

- `Experimental.P04_07.weight_five_spectral_cap_input`: Earlier 4.4 cap for the actual whitened operator on the exact 30n lattice; no root clustering assumed. Dependencies: P04_04.
- `Experimental.P04_07.weight_five_determinant_lower_input`: Earlier 4.6(1) actual normalized log-determinant lower rate; no finite-count or root-separation conclusion assumed. Dependencies: P04_06_PART1.
- `Experimental.P04_07.weight_five_primitive_height_input`: Earlier 4.6(2) upper naive height for the actual primitive polynomial. Dependencies: P04_06_PART2_UPPER.
- `Experimental.P04_07.integer_factor_height_input`: Classical integer factor-height bound with a conservative explicit 2^degree sqrt(degree+1) multiplier. Dependencies: CLASSICAL_GELFOND_MIGNOTTE_FACTOR_HEIGHT.

## Repair, interface and discharge obligations

- Discharge P04_04 and the specified P04_06 clauses on the same definitions and parameter lattice; they are not yet verified estimates.
- Supply the nonzero small primitive-center evaluation needed for the closest-root upper bound; the present scaffold does not assume or derive it.
- Formalize the finite cap-and-average argument, counted root multiplicities, reciprocal trace transport and the exact strict comparison 0.0140h>0.012K.
- Prove the integer-factor bound and a correct Mahler/discriminant separation inequality, including leading-coefficient and height normalization. Do not silently substitute coefficient height for Mahler measure without its extra factor.
- Keep O(K log K) as a quantified error with an explicit constant/onset before claiming the full original separation bound.

## Remaining work

Use actual spectral roots and the explicit upstream inputs to prove finite clustering and separation. Construct the primitive evaluation decay and quantitative factor-root separation before completing all clauses.

Each named axiom must be replaced by a proved declaration on these exact definitions and re-audited in the separately authorized execution target. A successful compile of an experimental axiom is not proof of its mathematical content.
