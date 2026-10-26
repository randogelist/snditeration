# Experimental manuscript item 6.1

**Theorem 6.1: Divided-difference $p$-adic valuation law and intrinsic $p^{-6}$ barrier**

Status: **SOURCE_ONLY_UNCOMPILED**. This is an isolated assumption interface,
not a completed theorem, an accepted witness or an A-Tier certificate.
The verified `Zetahyperbolic` umbrella is imported unchanged. The experimental
axioms are confined to `Experimental.P06_01` and must not enter its verified import graph.

## Verbatim manuscript statement

Source: supplied 52-page manuscript, 21 October 2026, page 29.
The following text is preserved verbatim from the extracted original TeX statement.

```tex
\label{thm:div-diff-barrier}
Let $M_{r_1, r_2}^{(7)} := \iint_{(0,1)^2} x_1^{r_1} x_2^{r_2}\,d\Omega_7(x_1, x_2)$ be the moment matrix of Theorem 5.1 for $0 \le r_1, r_2 \le K$.
\begin{enumerate}
\item \emph{(Multiplicative fiber reduction)} Under the change of variables $x_1 = u^y$, $x_2 = u^{1-y}$ ($u \in (0, 1)$, $y \in (0, 1)$) with Jacobian $\big|\frac{\partial(x_1, x_2)}{\partial(u, y)}\big| = -\log u$, for any polynomials $A(x) = \sum_{r=0}^K a_r x^r$ and $B(x) = \sum_{r=0}^K b_r x^r$ in $\mathbb{Q}[x]_{\le K}$, the two-variable integral reduces to the one-variable Mellin integral
\begin{equation}\label{eq:mellin-fiber}
\iint_{(0,1)^2} A(x_1) B(x_2)\,d\Omega_7(x_1, x_2) = \int_0^1 \mathcal{M}_{A, B}(u)\frac{(-\log u)^6}{720(1 - u)}\,du,
\end{equation}
where
\[
\mathcal{M}_{A, B}(u) := \int_0^1 A(u^y) B(u^{1-y})\,dy = \sum_{r=0}^K a_r b_r u^r + \sum_{0 \le r_1 \neq r_2 \le K} a_{r_1} b_{r_2}\frac{u^{r_1} - u^{r_2}}{(r_1 - r_2)\log u}.
\]
\item \emph{(Exact $p$-adic valuation of off-diagonal divided differences)} Let $p \ge 11$ be a prime in the outer range $K/2 < p \le K$. While every individual harmonic number $H_r^{(6)}$ ($0 \le r \le K$) has $p$-adic valuation $v_p(H_r^{(6)}) \ge -6$, the off-diagonal moment $M_{r_1, r_2}^{(7)} = \frac{H_{r_1}^{(6)} - H_{r_2}^{(6)}}{6(r_1 - r_2)}$ ($r_1 \neq r_2$) satisfies $v_p(M_{r_1, r_2}^{(7)}) = -7$ whenever $0 \le r_1 < p \le r_2 \le K$ and $r_1 \equiv r_2 \pmod p$.
\item \emph{(Non-degeneracy of the local pole obstruction)} In every residue class $\rho \in \{0, 1, \dots, p - 1\}$ with $L_\rho := \#\{0 \le r \le K : r \equiv \rho \pmod p\} = 2$ (so $r \in \{\rho, \rho + p\}$ with $\rho \le K - p$), the $2 \times 2$ local submatrix $\big[M_{\rho + l_1 p, \, \rho + l_2 p}^{(7)}\big]_{0 \le l_1, l_2 \le 1}$ at $X \in \mathbb{Z}_p$ has exact $p$-adic pole denominator $p^{-7}$ both on the diagonal ($l_1 = l_2 = 1$) and off the diagonal ($l_1 = 0, l_2 = 1$). Its leading $p^{-7}$ coefficient matrix $\begin{pmatrix} 0 & 1/6 \\ 1/6 & -1 \end{pmatrix}$ has determinant $-\frac{1}{36} \in \mathbb{Z}_p^\times$, so no non-zero $\mathbb{Z}_p$-linear combination of columns inside class $\rho$ can simultaneously annihilate the $p^{-7}$ pole on and off the diagonal.
\end{enumerate}
```

## Upstream paper items

- [5.1](https://github.com/randogelist/snditeration/blob/experiment/zetahyperbolic-p05-01_construction/Experimental/P05_01/Target.md)

## Imported facts and definitions

- `ManuscriptChain.Beukers.diagonal_moment`
- `ManuscriptChain.Beukers.offdiagonal_moment`
- `ManuscriptChain.Beukers.theorem_5_1_exact_moments`

## Explicit interface coverage

Encodes the actual unit-square moments, proposed fiber map, transformed integrand and finite harmonic residual. Existing monomial moment identities are imported, not axiomatized.

Every additional named axiom is enumerated in [Assumptions.json](Assumptions.json)
and spelled out over concrete mathematical data in [Prerequisites.lean](Prerequisites.lean).
No axiom assumes this target, `False`, or an unconstrained proposition.

## Exact repair and discharge obligations

No repair is silently substituted for the verbatim target.

Prove the fiber change-of-variables/Jacobian theorem and Mellin divided-difference formula; discharge harmonic residual integrality; derive exact crossing-index valuation and invertibility of the displayed local leading block. No determinant valuation is a prerequisite axiom.

For any later proposed proof: record the exact theorem type, keep all open
prerequisites visible, compile only on the authorized target, inspect its complete
transitive axiom list, and distinguish conditional experimental proof from the
original unconditional manuscript statement. A successful build retaining any
research axiom cannot certify the original result.
