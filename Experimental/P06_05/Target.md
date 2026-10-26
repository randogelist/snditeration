# Experimental manuscript item 6.5

**Theorem 6.5: Unconditional $q$-adic non-vanishing for $\Delta_K^{(\beta(4))}(0)$**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_05` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 34.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:beta4-qadic}
Let $q > 7$ be a prime satisfying $q \equiv 1 \pmod 8$, and set $m_q := \frac{q - 1}{8} \in \mathbb{Z}_{>0}$. Choose $N = 4 m_q = \frac{q - 1}{2}$, $K = 5 m_q = \frac{5(q - 1)}{8}$, $h = K - N = m_q = \frac{q - 1}{8}$, and $2m = 2$ in $G_K^{(\beta(4))}(X)$. Then at $X = 0$, the rational determinant $\Delta_K^{(\beta(4))}(0) = \det G_K^{(\beta(4))}(0) \in \mathbb{Q}$ satisfies the exact $q$-adic valuation
\[
v_q\big(\Delta_K^{(\beta(4))}(0)\big) = -(3 m_q - 2) < 0.
\]
In particular, $\Delta_K^{(\beta(4))}(0) \neq 0$ unconditionally for every prime $q \equiv 1 \pmod 8$ with $q > 7$.
```

## Upstream paper items

- [2.5](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p02-05_construction/Experimental/P02_05/Target.md)
- [5.3](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-03_construction/Experimental/P05_03/Target.md)
- [6.4](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p06-04_construction/Experimental/P06_04/Target.md)

## Imported facts and definitions

- `ManuscriptChain.PoleDiagonalization.lagrangeCoefficientMatrix_eq_inverse`

## Explicit interface coverage

Encodes the exact finite β-harmonic sums, odd-pole denominator and q-dependent parameters. It does not introduce an unconstrained matrix in place of the missing actual β(4) pencil.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

No repair is silently substituted for the verbatim target.

First finish the actual one-variable β(4) functional/pencil object and its 6.4 Lagrange transport; prove residual arithmetic, valuations of actual pole factors and the off-diagonal integrality/diagonal dominance. Finally derive the determinant valuation including change-of-basis factors. No diagonal or final valuation is assumed.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
