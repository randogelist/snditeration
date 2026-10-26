# Experimental manuscript item 6.9

**Theorem 6.9: Triple-pole and multi-weight Hankel determinants**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_09` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 38.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:multipole-extensions}
\begin{enumerate}
\item \emph{(Triple-pole Hankel architecture and consecutive-weight parity law)} For $n \ge 1$, let $R_n^{(3)}(t) := \frac{((6n)!)^3 \prod_{j=1}^n (t - j + 1)^6}{\prod_{k=0}^{6n} (t + k)^3}$. Under the polylogarithmic residue functional $\mathcal{L}_{\mathrm{poly}}^{(s)}((t + k)^{-r}) := (-1)^{r-1}\binom{s+r-2}{r-1}(\zeta(s+r-1) - H_k^{(s+r-1)})$ ($r = 1, 2, 3$), the Laurent expansion of $R_n^{(3)}(t) P(t)$ ($\deg P < 6n$) at $t = -k$ couples three consecutive weights $\{1, \zeta(s), \zeta(s+1), \zeta(s+2)\}$, and cannot annihilate $\zeta(s+1)$ identically across $\mathbb{Q}[t]_{< 6n}$ because the leading pole coefficient $C_{n, k}^{(3)} = (-1)^k \binom{6n}{k}^3 \binom{n+k}{k}^6 n! \neq 0$. Moreover, if $a_0 \zeta(s) + a_1 \zeta(s+1) + a_2 \zeta(s+2) = c$ ($a_0, a_1, a_2, c \in \mathbb{Z}$, $a_2 \neq 0$, $s \in \{3, 4\}$), then for every prime $q > \max(|a_2|, 13)$ with $q \equiv 1 \pmod 9$, setting $m = (q - 1)/9$ and $n = 2m$, the $3m \times 3m$ triple-pole Hankel determinant $J_{2m}^{(3)} := \det_{0 \le i, j < 3m}[\mathcal{L}_n^{(3)}(t^{i+j})]$ satisfies $v_q(J_{2m}^{(3)}) = -3(s + 3)m < 0$, and in particular $J_{2m}^{(3)} \neq 0$.
\item \emph{(Simultaneous multi-weight double-pole non-vanishing)} Let $2 \le s_1 < s_2 < \dots < s_d$ be any $d \ge 1$ distinct integers, and suppose $\sum_{r=1}^d a_r \zeta(s_r) = c$ with $a_1, \dots, a_d, c \in \mathbb{Z}$ and $a_d \neq 0$. In the double-pole functional $\mathcal{L}_n(P)$ of Theorem 5.7, replace $U_k, V_k$ by
\[
U_k^{[\mathbf{s}]} := c - \sum_{r=1}^d a_r H_k^{(s_r)}, \qquad V_k^{[\mathbf{s}]} := \sum_{r=1}^d \frac{a_r}{s_r k^{s_r + 1}} \quad (V_0^{[\mathbf{s}]} := 0),
\]
and set $J_n^{[\mathbf{s}]} := \det_{0 \le i, j < 3n}[\mathcal{L}_n^{[\mathbf{s}]}(t^{i+j})] \in \mathbb{Q}$. Then for every prime $q > \max(|a_1|, \dots, |a_d|, s_d + 5)$ satisfying $q \equiv 1 \pmod 9$, setting $m = (q - 1)/9$ and $n = 2m$, we have
\[
v_q\big(J_{2m}^{[\mathbf{s}]}\big) = -6 s_d m = -3 s_d n < 0,
\]
and in particular $J_{2m}^{[\mathbf{s}]} \neq 0$ (specifically $v_q(J_{2m}^{[3, 5, 6]}) = -36 m < 0$ for $\{1, \zeta(3), \zeta(5), \zeta(6)\}$).
\end{enumerate}
```

## Upstream paper items

- [2.5](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p02-05_construction/Experimental/P02_05/Target.md)
- [5.7](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-07_construction/Experimental/P05_07/Target.md)
- [6.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p06-01_construction/Experimental/P06_01/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Real.harmonic`

## Explicit interface coverage

Encodes the actual printed triple-pole rational function and lower-level finite decomposition, Hermite interpolation, and harmonic residue interfaces. The companion Hermite mod-p theorem is donor evidence only and is not silently imported.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

STATIC_SOURCE_REVIEW_PENDING_CONSISTENCY: at k=0 and n≥1, the displayed numerator contains the j=1 factor t^6 while the displayed denominator contains t^3. The apparent k=0 pole cancels. Consequently the printed claim that the leading triple-pole coefficient is nonzero at every k, including k=0, cannot be admitted as a prerequisite. Reconcile the actual rational function, index range and residue formula before proceeding. The experimental partial-fraction existence axiom permits zero coefficients and remains unchanged; this note is not a proof of the target.

Check the printed leading-pole coefficient and scaling exponents against the explicit rational function before asserting a normalization. In particular the determinant-scale calculation must use an actual field/scaling construction, not formal half-integer q powers.

Discharge decomposition and interpolation; compute and check actual Laurent coefficients, construct the polylog functional and determinants, establish noncancellation on the stated polynomial space, then identify exact mod-q Hermite blocks. For part (2), first implement the actual multiweight double-pole functional from5.7. Neither asserted determinant valuation nor the required block congruences are axioms.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
