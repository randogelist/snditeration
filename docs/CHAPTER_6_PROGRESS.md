# Chapter 6 proof campaign and exact remaining obligations

The literal chapter is not proved and cannot be certified unchanged: several
printed assertions have counterexamples. This campaign proves independent
valid clauses and corrected statements, while preserving the originals and
their repair gates. The proof branch is retained and unmerged. Original
completion remains **13/45 in verified PR source, 9/45 integrated on main**;
within Chapter 6, **6.2 is the sole whole original completed**. Corrected 6.1
remains complete separately with its earlier immutable evidence.

## Compiler evidence

Source [`3989d955e6190ab8fabc0720fad136b7e265e074`](https://github.com/randogelist/snditeration/tree/3989d955e6190ab8fabc0720fad136b7e265e074) passed [GitHub CI 40343849640](https://github.com/randogelist/snditeration/actions/runs/40343849640), job [121645398921](https://github.com/randogelist/snditeration/actions/runs/40343849640/job/121645398921), on 26 October 2026. The tested PR merge checkout was `c6c4708f5e0147bb426f0185adef4c02b06f8b16`; its entire tree is identical to the source tree.

The root build completed **8,897 build jobs**, importing **190 library modules**. The transitive audit checked **2,779 theorem declarations / 3,319 project declarations**. The 791 printed axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the all-project allowlist audit and source-placeholder scan passed. Lean **4.33.0**, Mathlib **db584cd6d46c92f209a44c0f1c829460d327499d**, dependencies and workflow remain pinned and unchanged. The preceding 169 library source blobs are unchanged; all 21 new modules are imported and audited.

[Immutable receipt and source fingerprints](receipts/CHAPTER_6_20261026.json) · [Full compiler/audit log](receipts/CHAPTER_6_CI_40343849640.log). The archived log has SHA-256 `68deaca90a50d56ca8144b3761a9a5bfbae302d21bee3df65b4d64d2f4f9c7e2`.

All new modules are imported by the certified root, and all project
declarations are inspected transitively. Experimental branches and their
custom prerequisites are separate. No local Lean execution, branch merge,
branch deletion, finite-witness closure or admission occurred.

## New verified scope

| Item | Result | Scope boundary |
| --- | --- | --- |
| 6.3(1) | Exact valuation −7q and nonvanishing of the full q-dimensional paired-monomial determinant, for every prime q≥5 and every q-integral rational evaluation; actual Beukers integral and affine-pencil identification. | Part (2) is false. The result is independent of its cone construction. |
| 6.4 | Literal surviving odd-square residues are positive in every dimension; exact polynomial partial fractions and a rational affine pencil with positive slope and real spectrum. The printed differential coupling is negative; its explicit correction is positive. | No certification of the printed beta integral calibration or of the whole theorem. |
| 6.5 | Actual integer polynomial quotient and odd-prime integrality of its Euler moments; local beta pole valuations. | Full Lagrange-congruence integrality, prefix/tail units and determinant valuation remain open. |
| 6.7(1) | Exact multiweight rational pencil, derivative CCᵀ, full degree h and reality of every complex root, for arbitrary rational independent polynomial families and integer weights. | No assumption of a signed integral realization or definite Krein cone is used. Parts (2) and (3) are separate. |
| 6.10(2) | Complete finite bound 1≤det(CCᵀ)≤(K+1)^h K^(2Ah), for every real A≥0, and log(det(CCᵀ))/K²→0 with h=floor(λK). Polynomial independence implies the required real rank; actual pencil slope is identified. | Part (1)'s equilibrium limits, strict reweighting and numerical ratio remain separate. |
| 6.13 | All-order central-factorial differential identity and low-mode annihilation, explicit positive exponential envelope, integrability of every polynomial moment, and strict positivity of every literal rational-kernel Gram matrix. | The printed series needs (−1)^(k−1); infinite-series differentiation, coupled beta-functional identity, slope and strict Newton hypotheses are not supplied. |
| 6.15(2)(ii), finite clauses | Actual determinant is affine with nonzero slope for every positive dimension; its unique rational root, parity-directed side, exact inverse-Gram error, an explicit polynomial error bound and convergence at fixed k,N are proved. | No geometric/polynomial asymptotic prefactor, Euler evaluation, transcendence or effective irrationality bound is inferred. |
| 6.16, repaired local bound | For the actual alternating odd harmonic sum, 2M≤p^(a+1) implies v_p(H_M^(β,s))≥−sa. In particular, 4j≤p² implies the intended bound for H_(2j). | A prime-size restriction is required for the uniform assertion; this cutoff is sufficient. It does not prove a global multiplier or zero-overhead rate. |

## Mathematical core of the new proofs

For **6.3(1)**, write A_r(x)=x^r+x^(r+q), 0≤r<q, and scale the full
matrix by q^7. Below q the harmonic sums are q-integral. In the outer
window the only q-divisible denominator is q itself, so
H_(r+q)^(s)−H_r^(s)=q^(−s)+a q-integral remainder. The diagonal paired
entry therefore has leading coefficient −1+2/6=−2/3 at order q^−7.
For distinct residues every cross difference is a q-adic unit, and its
entry has valuation at least −6. Consequently the scaled whole matrix
reduces to (−2/3)I modulo q. Since q≥5, its determinant is a unit, giving
v_q(det G)=−7q. A q-integral X adds 2X·I, which does not change this
reduction. The formal proof also identifies these entries with the
literal Beukers integrals.
The argument uses the sufficient scaled remainder of norm less than one;
it does not assume the stronger unscaled diagonal integral-remainder
congruence printed in the manuscript's proof.

For **6.7(1)**, the harmonic constants give a symmetric matrix H and the
single collapsed variable Z gives G(Z)=H+ZCCᵀ. Independence of the
rational polynomials implies full row rank after real scalar extension,
so M=CCᵀ is positive definite. Conjugating by M^(−1/2) gives
M^(−1/2)HM^(−1/2)+ZI. This is a real symmetric matrix plus ZI; its
determinant is a nonzero constant times h real linear factors. Thus the
degree is exactly h and every complex zero is real, independently of the
signs of the weights or any Krein-space claim.

For **6.10(2)**, the integer Gram determinant is a positive integer, so
it is at least one. Each diagonal entry is a sum of K+1 coefficient
squares and is at most (K+1)K^(2A). Hadamard gives the exact printed upper
bound. With h=floor(λK), its logarithm is O(K log K), and division by
K² tends to zero. The formal proof derives real row independence from
the actual integer polynomials and handles every real A≥0.

For the finite **6.15** pencil, the actual slope is (−1)^N vvᵀ. Applying
the matrix determinant lemma at the positive beta Gram matrix A gives

`det G(X) = det A * (1 + (−1)^N (X−beta) vᵀ A^−1 v)`.

The inverse quadratic form is positive. This proves the unique root,
its parity-directed side and its exact error. Rational coefficients make
the root rational: it equals −det G(0)/(det G(1)−det G(0)).
Cauchy–Schwarz in the A-inner product bounds this error by the last
diagonal moment. In dimension h+1 this is at most
1/(2(N+2h)+1)^(2k+1), which tends to zero at fixed k,N.
This proves convergence without assuming the printed stronger asymptotic.

## Refutations and corrections

* **6.3(2): independent exact-rational replay.** At h=4, K=28, four
  independent normalized basis polynomials satisfy all 12 printed
  orthogonality constraints for each basis polynomial (48 exact checks). A nonzero combination has quadratic value
  strictly between −1.2115×10^−48 and −1.2114×10^−48. The zeta enclosure
  uses 240 Euler-transform terms with a proved elementary remainder bound.
  This replay is mathematical/computational evidence, **not a Lean kernel
  replay and not `!!`**. The immutable certificate, both checkers and hashes
  are recorded separately below.
* **6.4(1):** the actual displayed coupling equals
  −π y⁴ sinh(πy/2)/(16 cosh⁴(πy/2)), which is negative for y>0. Multiplying
  it by −π gives the displayed positive π² normalization. This corrects
  the differential expression only; it does not establish its claimed
  arithmetic functional identification.
* **6.7(2) and 6.17(2):** positive and negative h-dimensional subspaces of
  the same degree-K coefficient space must be disjoint, hence 2h≤K+1.
  The permitted choice K=h=2 refutes the fixed-degree cone conclusions.
  Allowing sufficiently large degree is a necessary repair, not a proof
  of existence or infinite-tail control.
* **6.14(1):** its own displayed monomial formula at r=1,e=2 is −25/256,
  with v_5=2. Thus its claim of valuation exactly zero at every odd prime
  is false. Odd-prime integrality is weaker and must be stated separately.
  The independent Jacobian and functional-normalization conflicts remain.
* **6.16(3):** the actual H_26^(β,2) has v_7=−4, contradicting the printed
  unrestricted ≥−2 bound. The prime and coefficient-size hypotheses are
  satisfied. The repaired cutoff above prevents this prime-square term.
* Existing **6.1** nonzero-vector and **6.9** origin-coefficient refutations
  retain their earlier immutable source and run receipts.

The secant source parameter equals the manuscript parameter minus one; this shift is explicit when comparing differential factors and signs.

## All eighteen original items

| Item | Whole-original status and remaining obligation |
| --- | --- |
| 6.1 | False nonzero-vector clause. Exact (1)–(2) and complete primitive-vector correction verified separately. |
| 6.2 | Whole original complete on verified PR source; main integration remains pending. |
| 6.3 | Exact (1) complete; (2) needs a new positive-subspace construction and quantitative negative-tail control. |
| 6.4 | Differential expression false as printed; actual beta monomial/pole integral calibration must be repaired. Finite residue/pencil results survive independently. |
| 6.5 | Next independent arithmetic endpoint: derive the complete selected-prime Lagrange matrix and valuation −(3m_q−2) from the actual rational pencil. |
| 6.6 | Actual shifted multiweight functional, summability, two-sided density comparison and all-prime multiplier rate remain open. |
| 6.7 | Exact (1) complete; fixed-K cones false; arbitrary-L² identity and top-active-weight determinant are separate open targets. |
| 6.8 | Depends on unproved 4.5 arithmetic/decay. Taking a=0 already requires ζ(5) irrationality. Effective exponent and threshold remain open. |
| 6.9 | Printed leading triple-pole coefficient refuted uniformly; corrected pole support, Hermite congruences and valuation remain open. |
| 6.10 | Exact (2) complete; actual equilibrium limits, strict reweighting and claimed numerical ratio in (1) remain open or require repair. |
| 6.11 | Euler distribution, odd/2-adic quotient valuations and quantitative denominator laws remain open. |
| 6.12 | Repaired beta calibration, actual spectral margin, explicit rational cutoff and local determinant remain open. |
| 6.13 | Corrected analytic operator/Gram components complete; series interchange, beta-functional/slope identification and strict Newton condition remain open. |
| 6.14 | Scaling identities conflict and universal odd-prime unit claim is false; choose one consistent functional/measure normalization before coupled spectral bounds. |
| 6.15 | Actual positive measure, all-order moments/minors and finite rational root established; Euler evaluation, effective arithmetic and precise asymptotics remain open. |
| 6.16 | Unrestricted harmonic bound false; corrected cutoff proved. Mixed weights, endpoint ratios, affine identification and separated small/large-prime estimates remain open. |
| 6.17 | Fixed-K cones false and prior q=11/q=41 proof-step counterchecks remain. Actual normalization, infinite Krein convergence and recomputed determinant are open. |
| 6.18 | Quotient disappearance alone does not prove dyadic integrality, zero height loss or effective measures; inherited cone and arithmetic assumptions remain open. |

## Independent rational certificate

The original certificate and published checker are from companion source
`86ca99a23d65cde4880a9005a49076c43e7bc968`, blobs
`855f5f517fccafc45ff689cb872580b881ae0447` and
`84f1fac82da4147824098add6b84ccef410c8d0d`. They are preserved byte-for-byte.
The separate checker recomputes the Euler enclosure by forward differences
and the quadratic form by unordered off-diagonal pairs. It also checks the
normalized basis and the exact negative-direction coordinates.

For the analytic enclosure, integrate the finite identity

`1/(1+x) = Σ_(j<N) (1−x)^j/2^(j+1) + (1−x)^N/(2^N(1+x))`

against `(-log x)^6/720` on (0,1). This positive weight has mass one,
so the remainder lies in [0,2^−N]. Absolute convergence at weight seven
gives eta(7)=(63/64)zeta(7). All subsequent inequalities are exact fractions.

No prior publication receipt or experimental branch target is overwritten.

Archived exact-rational replay: [certificate](receipts/CHAPTER_6_COUNTEREXAMPLE_6_3/provenance/beukers_cone_h4_certificate.json), [published checker](receipts/CHAPTER_6_COUNTEREXAMPLE_6_3/tools/check_beukers_h4_counterexample.py), [independent checker](receipts/CHAPTER_6_COUNTEREXAMPLE_6_3/independent_review.py), and [independent replay receipt with hashes](receipts/CHAPTER_6_COUNTEREXAMPLE_6_3/independent_review_receipt.json).
