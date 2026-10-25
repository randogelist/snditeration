# Cross-branch closure audit — 2026-10-25

**Purpose:** decide which manuscript gaps can genuinely be crossed off after comparing the active Lean branches in `randogelist/snditeration` and `randogelist/zetahyperbolic-axiom`. This is a *proof evidence review*, not a new Lean build. It does not silently copy proofs between repositories.

## Evidence pinned and inspected

| Evidence | Exact source |
|---|---|
| Original manuscript | 52-page PDF (21 October 2026), SHA-256 `935767c0cda7468f376cd8eadc374077caf6c8a060351d3bea26ac3f838a9d0c` |
| Local verified repository | [`snditeration/main@c521749`](https://github.com/randogelist/snditeration/commit/c521749190cce9981b0f108a8edc8034420f6420), [CI run 40186793090](https://github.com/randogelist/snditeration/actions/runs/40186793090), [846-declaration checkpoint](https://github.com/randogelist/snditeration/blob/c521749190cce9981b0f108a8edc8034420f6420/CHECKPOINT.json) |
| Companion verified repository | [`zetahyperbolic-axiom/main@86ca99a`](https://github.com/randogelist/zetahyperbolic-axiom/commit/86ca99a23d65cde4880a9005a49076c43e7bc968), [CI run 40188664869](https://github.com/randogelist/zetahyperbolic-axiom/actions/runs/40188664869), [219-module acceptance](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/validation/linux/acceptance.json), [transitive proof-integrity report](https://github.com/randogelist/zetahyperbolic-axiom/blob/86ca99a23d65cde4880a9005a49076c43e7bc968/validation/linux/proof_integrity.json) |
| Continued local candidate | [`snditeration` PR #15](https://github.com/randogelist/snditeration/pull/15), head `0cee4ea2`, [CI run 40188938699](https://github.com/randogelist/snditeration/actions/runs/40188938699): **FAIL**, so its 51 changed files cannot close tracker items |
| Branch scan | 17 `snditeration` branches and 5 `zetahyperbolic-axiom` branches (including `main`, documentation branches, completed feature branches and in-progress branches) |

The companion run successfully compiled the project and ran its **actual transitive axiom gate**. Its pinned validation reports 2,489 theorem declarations (including generated/private), 3,135 project declarations and standard axioms only: `propext`, `Classical.choice`, `Quot.sound`. The local `snditeration` checkpoint records 846 audited theorem declarations. These figures are not manuscript theorem counts, nor independent proof reviews of every mathematical interpretation.

## Crossed off: exact printed theorems proved in at least one audited repository

A strikethrough here means **no longer mathematically missing from the combined audited Lean sources**. It does **not** imply the proof is already integrated into `snditeration/main`. The table explicitly distinguishes the two.

| Paper item | Aggregate status | `snditeration/main` | Exact source supporting closure |
|---|---|---|---|
| ~~Lemma 2.2~~ rational-functional pullback | **RESOLVED_LOCAL** | Complete | `Zetahyperbolic/Section2/RationalPullbackAssembly.lean` / `Mu` and companion `Section2MuLinear.mu_pullback` |
| ~~Lemma 2.3~~ reflection and difference identities | **RESOLVED_CROSS_REPO** | Reflection and algebraic difference complete; stronger all-domain derivative interface remains a local task | `src/LeanPaper/Section2RatFuncReflection.lean`, `Section2RatFuncTranslation.lean`, `Section2DifferenceDerivative.lean`; theorem `tau_difference_derivative` and `tau_difference_span_derivative` give actual `iteratedDeriv` divided by factorial for the **printed simple-pole span** |
| ~~Theorem 2.4~~ canonical basis invariance | **RESOLVED_LOCAL** | Complete | `Zetahyperbolic/Section2/BasisInvariance.lean`, `PoleDiagonalization.lean` |
| ~~Theorem 2.5~~ Lagrange pole diagonalization | **RESOLVED_LOCAL** | Complete | `Zetahyperbolic/Section2/PoleDiagonalization.lean`, `LagrangeBasis.lean` |
| ~~Theorem 3.1~~ universal hyperbolicity and sharp finite zero-free disk | **RESOLVED_LOCAL** | Complete **for the actual odd-weight family**, without quantitative exponential exponent or root simplicity | `Zetahyperbolic/Section3/Unconditional.lean`, `ActualSpectrum.lean`, `PrimitivePolynomial.lean` |
| ~~Proposition 4.3~~ complex p-adic zero-free disk | **RESOLVED_CROSS_REPO** | Not yet imported / main-audited | `src/LeanPaper/ImportedSection4/Proposition_4_3_{PadicDisk,IsometricExtension,ComplexPadicDisk}.lean`: `PROPOSITION_4_3_INTEGER_COMPLEX_PADIC` proves exact norm preservation and nonvanishing at every `α : ℂ_[p]` in the stated disk |
| ~~Theorem 5.4~~ higher-zeta cancellation on even pole pairs | **RESOLVED_CROSS_REPO** | Not yet imported / main-audited | `src/LeanPaper/Section2TauLinear.lean`: `evenPolePair_cancellation`, `evenPolePair_coe` for actual `RatFunc` and all `j≥1`; independent proof fixes errors in the printed intermediate manipulations |

**Total across the two audited repositories: 7/45 complete printed items** (4 with verified local `main` scope plus 3 additional complete companion items). The next best import candidates are **2.3, 4.3 and 5.4**. Rebuild and transitive-audit each in `snditeration` before promoting its *local* status to `RESOLVED_LOCAL`.

**Important nuance for 2.3:** The full *printed* pole/span derivative statement is proved externally. `snditeration`'s separate proposed identity between its specific `partialFractionCoefficient` and analytic derivatives for **all regular rational-domain functions** is a potentially stronger local integration endpoint and stays open until that exact Lean type has been proved; it is not grounds for withholding the completed printed 2.3 from aggregate closure.

## Resolved proper subclauses or corrected counterparts — not complete original theorems

| Gap ID | Proven component in audited sources | Why the complete printed item stays open/blocked |
|---|---|---|
| `P03.02` | Corrected all-real-`s>1` positive Gram/hyperbolicity and correct odd-`s` coincidence, `LeanPaper.ContinuousGram` / `ContinuousDensityNormalization` | Printed density is multiplied by `π/2`. Only **corrected variant** can be closed; literal original **REPAIR_REQUIRED** |
| `P03.04b` | **Entire universal Dodgson/at-minor-root subclause** for actual finite Hankel pencil: `LeanPaper.DodgsonCondensation.manuscript_condensation`, `manuscript_at_minor_root` | No complete corrected rank-aware Cauchy interlacing; **Theorem 3.4 as a whole remains blocked/partial**. This proper subclause can be crossed off at **cross-repo** scope |
| `P03.06` | All-order **corrected** finite-atomic reciprocal moments, log derivatives, rank-sensitive Hankel law and nearest-root limit, `LeanPaper.CorrectedReciprocalCorollary.corrected_corollary_3_6`; local corrected estimates already audited | Printed all-orders **strict** determinant positivity, direction of bound and odd-derivative sign are false. Original Cor. 3.6 **REPAIR_REQUIRED**, not proved verbatim |
| `P03.07` | Actual-family root distinctness and strict normalized Newton/centered inequalities, `LeanPaper.ActualStrictNewton` | Nonvanishing of every individual intermediate centered coefficient is not established and does not follow from distinctness; other printed equality claims must be checked |
| `P04.01` | Generic integer-polynomial squeeze on `snditeration/main` plus effective index/threshold construction **with explicitly supplied computable onset/rates**, `LeanPaper.Section4IndexSelection`, `Section4EffectiveBudget`, `Section4TransferComplete` | Printed phrase “effectively computable” from bare *eventually* hypotheses needs constructive rate data. Actual ζ(5) family bounds remain wholly open |
| `P05.02a` | Finite coefficient Gram slope `CCᵀ` and symmetric dual spectrum, companion `ImportedSection56/PositiveSlopeSpectrum.lean` and `Section5DualSpectrum.lean` | Continuous measure/infinite Krein identity/strict polynomial cone construction still unproved |
| `P06.02` | Exact rational dual constants, harmonic divided differences and `6·d_K^7` denominator, `LeanPaper.BeukersDenominator` | True two-variable integral and simultaneous forms not yet completed |
| `P06.10b` | Finite coefficient Gram-slope positivity `LeanPaper.ImportedSection56.CoefficientGram` | Full **uniform** `K`-growth rate/height asymptotic remains open; local PR #15 source `CoefficientGramGrowth` fails CI |
| `P06.13` | Finite central-factorial secant identity and corrected sign, `LeanPaper.CentralFactorialSecant`, plus exponential envelope `CentralFactorialDecay` | Printed series requires `(-1)^(k-1)`; differentiated *infinite* series and beta pencil transfer remain open |
| `P06.15` | Qualitative odd-beta evaluation/transcendence and finite ℚ-linear independence with 1, `LeanPaper.OddBetaValues` and pinned audited Lindemann intake | Printed *effective measures* and fixed exterior Christoffel rate remain open; exterior `h^(-2k)` factor conflicts with cited Szegő asymptotics |
| `P06.18` | Exact polynomial-quotient degree/threshold identities, `LeanPaper.DyadicQuotientThreshold` | Principal-minor 2-adic integrality, uniform height and irrationality measure remain open |

These are deliberately **subclause closures**. Their parent 45 numbered items are **not** additional successes in the 7/45 complete count.

## Resolution of a false printed formula is not proof of that formula

- **3.2** incorrect normalization: corrected full pencil proved externally; keep literal 3.2 flagged for source repair.
- **3.5** printed continued fraction: actual rank-one counterexample locally verified; full corrected Jacobi/Lanczos still open.
- **3.6** all-order strict finite-atom moment determinants: mathematically impossible, with actual-family counterexample and corrected theorem proved. Do **not** count verbatim printed claim as complete.
- **3.7** “distinct eigenvalues imply all intermediate coefficients nonzero”: invalid general inference; actual sign regularity, if true, needs a separate theorem.
- **5.2(3)** fixed-`K` dimension restriction and uncontrolled negative Krein tail: dimension obstruction verified externally; corrected quantifier required.
- **6.3(2)** external rational **h=4** negative quadratic certificate refutes the stated positive cone. It is not yet a Lean kernel-checked counterexample, and a *new* subspace construction is needed.
- **6.13** sign of central-factorial series must be corrected; the finite operator identity is kernel-verified.
- **6.15(2)(ii)** fixed exterior asymptotic `h^(-2k)` conflicts with Szegő asymptotics; this analytic diagnosis is not a Lean kernel proof.
- **6.17(3)(ii)** external code checks specific false odd-harmonic denominator and leading q-adic claims. The full hypothetical theorem is not thereby disproved.

## Branch resolution policy

`RESOLVED_LOCAL` = exact compiled/axiom-audited `snditeration/main` declaration and original manuscript correspondence.

`RESOLVED_CROSS_REPO` = exact compiled/axiom-audited theorem at the **pinned companion commit**, source correspondence reviewed, but no claim of import to `snditeration/main`.

`RESOLVED_CORRECTED_ONLY` = a proved *replacement*, retaining `REPAIR_REQUIRED` for the literal printed text.

`RESOLVED_SUBCLAUSE` = a completed proper component, **not** an additional complete printed manuscript item.

`CANDIDATE_FAILED` = open/failed integrated PR. Keep the 51-file [PR #15](https://github.com/randogelist/snditeration/pull/15) in this category until a successful complete build and transitive axiom check.

No full Leaned Paper, unconditional ζ(5)/ζ(7) irrationality, RH, or finite-witness/S-Tier conclusion follows from these receipts.
