# Experimental paper item 3.7: Tur\'anian non-negativity and Newton log-concavity

Status: **SOURCE_ONLY_UNCOMPILED**. This branch is a typed experimental boundary, not a proof certificate. No Lean execution was performed. Existing proof facts retain their original source receipts; the new files have no compile/audit receipt.

## Original statement (verbatim source TeX)

PDF page 11; source label `thm:turan-newton`. The following text is copied without correction from `manuscript_complete_inventory.json`.

```tex
\label{thm:turan-newton}
Fix any odd integer $s = 2k+1 \ge 3$ and integers $K > N \ge 1$ with $h = K - N \ge 2$ and $2m \ge 2$. Write $P_K^{(s)}(X) = \sum_{m=0}^h a_{K, m} X^m \in \ZZ[X]$ and let $\tilde{a}_{K, m} := a_{K, m}/\binom{h}{m}$.
\begin{enumerate}
\item For every $1 \le m \le h - 1$ and every $X \in \RR$, the Tur\'anian Wronskian satisfies
\begin{equation}\label{eq:Turan-ineq}
\mathcal{T}_m(X) := \left(\frac{d^m}{dX^m} P_K^{(s)}(X)\right)^2 - \left(\frac{d^{m-1}}{dX^{m-1}} P_K^{(s)}(X)\right) \left(\frac{d^{m+1}}{dX^{m+1}} P_K^{(s)}(X)\right) \ge 0,
\end{equation}
with strict inequality $\mathcal{T}_m(X) > 0$ at every $X \in \RR$ where $\frac{d^{m-1}}{dX^{m-1}} P_K^{(s)}(X) \neq 0$. In particular, at $X = \zeta(s)$, $\frac{P_K^{(s)\prime\prime}(\zeta(s))}{P_K^{(s)}(\zeta(s))} < \left(1 - \frac{1}{h}\right) \left(\frac{P_K^{(s)\prime}(\zeta(s))}{P_K^{(s)}(\zeta(s))}\right)^2$ with strict inequality.
\item Newton's log-concavity $\tilde{a}_{K, m}^2 \ge \tilde{a}_{K, m-1}\, \tilde{a}_{K, m+1}$ holds for every $1 \le m \le h - 1$. Strict inequality $\tilde{a}_{K, m}^2 > \tilde{a}_{K, m-1}\, \tilde{a}_{K, m+1}$ holds if and only if $\tilde{a}_{K, m} \neq 0$ or both $\tilde{a}_{K, m-1} \neq 0$ and $\tilde{a}_{K, m+1} \neq 0$. In the exceptional case $\tilde{a}_{K, m} = 0$ and ($\tilde{a}_{K, m-1} = 0$ or $\tilde{a}_{K, m+1} = 0$), equality $\tilde{a}_{K, m}^2 = \tilde{a}_{K, m-1}\, \tilde{a}_{K, m+1} = 0$ holds.
\item Let $e_m(\beta_1, \dots, \beta_h) := [Y^m]\frac{P_K^{(s)}(\zeta(s) + Y)}{P_K^{(s)}(\zeta(s))}$ be the shifted Taylor coefficients around $X = \zeta(s)$, and set $\tilde{e}_m := e_m(\beta_1, \dots, \beta_h)/\binom{h}{m}$ (with $\tilde{e}_0 := 1$). Then $\tilde{e}_m^2 \ge \tilde{e}_{m-1}\, \tilde{e}_{m+1}$ for every $1 \le m \le h - 1$, with strict inequality whenever $\tilde{e}_m \neq 0$ or both $\tilde{e}_{m-1}, \tilde{e}_{m+1} \neq 0$. Since all roots $-1/\beta_j = r_j - \zeta(s)$ are nonzero (Theorem~\ref{thm:hyperbolicity}) and not all equal (Theorem~\ref{thm:signature}(3)), the only exceptional case is a block of three consecutive zeros $\tilde{e}_{m-1} = \tilde{e}_m = \tilde{e}_{m+1} = 0$, which for real $\beta_j$ can occur only if the shifted polynomial has the symmetric structure $\prod_j (1 + \beta_j Y) = g(Y^q)$ for some $q \ge 3$; in the present construction, the $\beta_j$ are real eigenvalues of $B_K^{(s)}$ and, being a Hankel spectrum, are generically distinct, so $\tilde{e}_m \neq 0$ for all $1 \le m \le h - 1$ and the strict inequality $\tilde{e}_m^2 > \tilde{e}_{m-1}\, \tilde{e}_{m+1}$ holds throughout.
\end{enumerate}
```

## Prerequisites and direction

No new axiom. Existing verified upstream facts are exposed by typed aliases; the remaining target is not assumed.

## Existing upstream facts

- `Experimental.P03_07.actual_real_splitting` aliases `ManuscriptChain.NewtonTuran.Actual.primitiveRealPolynomial_splits` (paper dependency 3.1).
- `Experimental.P03_07.actual_center_nonzero` aliases `ManuscriptChain.NewtonTuran.Actual.primitiveRealPolynomial_center_ne_zero` (paper dependency 3.1).
- `Experimental.P03_07.actual_two_distinct_roots` aliases `ManuscriptChain.NewtonTuran.Actual.actual_primitive_hasDistinctRoots` (paper dependency 3.3(3)).

## Formula coverage and missing interfaces

Typed aliases only: actual primitive-polynomial real splitting, nonzero zeta-center value and existence of two distinct roots. These imported facts support the already-proved Turan/Newton inequalities; they do not prove individual centered-coefficient nonvanishing.

No new axiom is introduced: the relevant upstream spectral facts are already proved. Introducing individual coefficient nonvanishing, or a spectral condition chosen only to restate it, would assume the outstanding target. The named HasDistinctRoots predicate means existence of two distinct roots, not squarefreeness. The false generic-distinctness justification is preserved in the literal statement below, not endorsed.

## Integration and discharge obligations

1. Publish the files under `Experimental/P03_07/`; `Work.lean` imports only its named prerequisites, which import the existing active verified root `Zetahyperbolic`.
2. Elaborate this exact source in the authorized target with pinned Lean/Mathlib. Until that happens, even declaration syntax is unverified. Do not treat the old root CI receipt as evidence for these new modules.
3. Keep every new axiom named in `Assumptions.json` in the transitive audit report. Prove each exact quantified input before promotion; do not weaken the target, change the actual objects, or silently add new premises.
4. Record separately which original clauses are obtained and which remain open. Any corrected formulation must be separately named and must not replace the literal statement above.
5. A target proof using these inputs is an experimental conditional result. Only an exact discharged proof and successful source-bound compilation/axiom audit can change its status. This scaffold declares no target theorem and contains no placeholder proof.
