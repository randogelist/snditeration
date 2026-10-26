# Experimental manuscript item 6.2

**Theorem 6.2: Simultaneous weight-$(6, 7)$ Beukers functional with zero denominator overhead**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_02` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 31.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:sim-67}
Let $d\Omega_7(x_1, x_2) = \frac{1}{720}\frac{(-\log(x_1 x_2))^5}{1 - x_1 x_2}\,dx_1\,dx_2$ on $(0, 1)^2$. Then:
\begin{enumerate}
\item For every integer $m \ge 0$, $\iint_{(0,1)^2} x_1^m x_2^{m+1}\,d\Omega_7(x_1, x_2) = \frac{1}{6(m + 1)^6}$, and for every integer $r \ge 0$,
\begin{equation}\label{eq:zeta6-tail}
\iint_{(0,1)^2} \frac{(x_1 x_2)^r x_2}{1 - x_1 x_2}\,d\Omega_7(x_1, x_2) = \frac{1}{6}\big(\zeta(6) - H_r^{(6)}\big).
\end{equation}
\item For any polynomial $A(x) = \sum_{r=0}^K c_r x^r \in \mathbb{Z}[x]$ and any integers $\alpha, \beta \in \mathbb{Z}$, the single integral
\[
\mathcal{I}_K(\alpha, \beta; A) := \iint_{(0,1)^2} \left[\alpha A(x_1) A(x_2) + \frac{6\beta A(x_1 x_2) x_2}{1 - x_1 x_2}\right] d\Omega_7(x_1, x_2)
\]
evaluates to the exact simultaneous linear form in $\zeta(7)$ and $\zeta(6)$:
\[
\mathcal{I}_K(\alpha, \beta; A) = \alpha \left(\sum_{r=0}^K c_r^2\right) \zeta(7) + \beta \left(\sum_{r=0}^K c_r\right) \zeta(6) - R_K(\alpha, \beta; A),
\]
where the rational part
\[
R_K(\alpha, \beta; A) := \alpha \sum_{r=0}^K c_r^2 H_r^{(7)} - \frac{\alpha}{6}\sum_{0 \le r \neq s \le K} c_r c_s \frac{H_r^{(6)} - H_s^{(6)}}{r - s} + \beta \sum_{r=0}^K c_r H_r^{(6)} \in \mathbb{Q}
\]
satisfies $6 d_K^7 R_K(\alpha, \beta; A) \in \mathbb{Z}$ with the exact same denominator $6 d_K^7$ as the pure $\zeta(7)$ form.
\end{enumerate}
```

## Upstream paper items

- [5.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-01_construction/Experimental/P05_01/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Beukers.theorem_5_1_exact_moments`
- `ManuscriptChain.Beukers.integral_density_moment_series`

## Explicit interface coverage

Uses the verified density and moments directly; defines the exact lcm and inserted geometric-series terms. No simultaneous linear form evaluation or final denominator overhead is assumed.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

No repair is silently substituted for the verbatim target.

Prove both prerequisites, establish the extra geometric expansion and interchange, derive the ζ(6) tail, expand integer polynomial coefficients, and clear the divided-difference denominators. The target formula for R_K is not an axiom.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
