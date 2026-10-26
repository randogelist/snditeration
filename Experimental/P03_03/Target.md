# P03_03: Total positivity, leading sign, and universal signature

Status: SOURCE_ONLY_UNCOMPILED. These experimental inputs are not proof receipts, and custom axioms must be discharged before any unconditional claim. No Lean execution was performed.

## Original statement (verbatim manuscript TeX)

```tex
\label{thm:signature}
Fix $K > N \ge 1$ ($h = K - N$), $m \ge 1$, and an odd integer $s = 2k+1 \ge 3$.
\begin{enumerate}
\item The infinite moment sequence $\mu_r^{(s)} := \int_0^\infty t^r \frac{D_N(t)^{2m}}{D_K(t)} \frac{w_s(\sqrt{t})}{2\sqrt{t}}\,dt$ ($r \ge 0$, with $2m N \le K$) is a determinate Stieltjes moment sequence on $[0, \infty)$, and $G_K^{(s)}(\zeta(s))$ is strictly totally positive of all orders: every $r \times r$ minor $\det G_K^{(s)}(\zeta(s))[I, J]$ ($0 \le i_1 < \dots < i_r < h$, $0 \le j_1 < \dots < j_r < h$) is strictly positive.
\item In the weight-$5$ construction with $K = 30n, N = 3n, h = 27n,$ and $2m = 6$, the leading coefficient $a_{K, h} := [X^h] P_K^{(5)}(X)$ has exact sign $\sgn(a_{K, h}) = (-1)^{n(n-1)/2}$.
\item For every odd $s \ge 3$ and $2m \ge 2$, the matrix $B_K^{(s)}$ has signature $(\lceil h/2 \rceil, \lfloor h/2 \rfloor)$ if $N$ is even, and $(\lfloor h/2 \rfloor, \lceil h/2 \rceil)$ if $N$ is odd and $h$ is odd. In particular, for $K = 30n, N = 3n, h = 27n$, the signature of $B_K^{(5)}$ is universally $(\lfloor h/2 \rfloor, \lceil h/2 \rceil)$ for every $n \ge 1$, so $P_K^{(5)}(X)$ has $\lfloor 27n/2 \rfloor$ roots strictly below $\zeta(5)$ and $\lceil 27n/2 \rceil$ roots strictly above $\zeta(5)$.
\end{enumerate}
```

## Prerequisite direction and exact scope

Dependency direction for part (1): actual factorial moment bound → divergent Stieltjes Carleman series → measure uniqueness, with the uniqueness theorem still to supply. Generalized Vandermonde positivity → sign of the two alternants in an independently justified Andréief integral → strict positivity of actual mixed minors. Neither axiom is the full target or its matrix-minor/determinacy conclusion.

Both factorial constants are uniform over all moment orders r for a fixed admissible p; they may depend on p. The measure is literally ConcreteMoment.momentMeasure p, not an abstract unspecified sequence. The generalized Vandermonde input is independent finite algebra, with explicit positivity and order hypotheses.

Existing part (2) leading sign and part (3) multiplicity-counted inertia/root-side formulas remain imported proven results. Existing actual Gram positivity is a typed alias, not a new assumption. No pairwise root simplicity is asserted.

Missing domain interfaces/work: arbitrary mixed row/column lists, finite-product measure and Andréief integration, integrability of alternants, positive mass of ordered nodes, and an exact Stieltjes uniqueness criterion. The unimported MomentGrowth/CarlemanDivergence/ShiftedMomentPositivity/MixedMomentTwo files are only candidate discharge sources and are not imported here.

Integration/discharge: replace each named axiom by an exact proof; retain all r quantifiers and actual-measure identification; compile/audit experimental branch and then rerun a clean axiom-free downstream audit. Until then SOURCE_ONLY_UNCOMPILED, with all inherited custom axioms visible.

## Named typed inputs

- `Experimental.P03_03.actualMomentFactorialMajorant`: For each admissible actual manuscript measure, one positive constant and one fixed factorial offset bound every moment. Only the analytic growth input to a Stieltjes Carleman argument; not measure uniqueness.
- `Experimental.P03_03.generalizedVandermondePositive`: Generalized Vandermonde determinants are positive on strictly increasing positive nodes and strictly increasing natural exponents. Only pointwise integrand sign for mixed minors after an independently proved Andreief identity.

- `Experimental.P03_03.existingActualGramInput` reuses `ManuscriptChain.GRAM_POSITIVE`: Actual positive-definite Gram, already proved.
