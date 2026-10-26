# Experimental manuscript item 6.8

**Corollary 6.8: Unconditional three-term linear independence cone for $\{1, \zeta(3), \zeta(5)\}$**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_08` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 38.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{cor:three-term-cone}
For every non-zero integer triple $(c, a, b) \in \mathbb{Z}^3 \setminus \{(0, 0, 0)\}$ satisfying either $b = 0$ or $b \neq 0$ and $\frac{a}{b} < \frac{\pi^2}{3}$, the linear form $c + a\zeta(3) + b\zeta(5)$ is strictly non-zero. Furthermore, for any coprime integers $(a_0, b_0)$ with $b_0 > 0$ and $a_0 < \frac{\pi^2}{3}b_0$, there exists an effectively computable $Q_0(a_0, b_0) > 0$ such that for every integer $q \ge Q_0(a_0, b_0)$ and every $c \in \mathbb{Z}$, writing $(a, b) = q(a_0, b_0)$, we have
\[
|c + a\zeta(3) + b\zeta(5)| > q^{-25686}.
\]
```

## Upstream paper items

- [4.5](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p04-05_construction/Experimental/P04_05/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Real.zeta_eq_riemannZeta_re`

## Explicit interface coverage

The actual two-term form and precisely identified upstream Apéry/4.5 statements are typed. Nothing assumes the current nonzero three-term conclusion or its q^(-25686) bound.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

No repair is silently substituted for the verbatim target.

Obtain an accepted Apéry import and prove actual Theorem 4.5; normalize the sign of b and handle b=0 and a=0 separately. Derive integer-translate nonvanishing and the raywise bound by multiplying the upstream rational approximation estimate. A concrete computable threshold interface is still needed for the word effectively; the existential axiom does not certify effectivity.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
