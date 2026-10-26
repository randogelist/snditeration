import Zetahyperbolic
import Lean.Util.CollectAxioms

/-! Print transitive logical dependencies for selected manuscript declarations. -/
#print axioms ManuscriptChain.Real.zeta_eq_riemannZeta
#print axioms ManuscriptChain.Real.zeta_pos
#print axioms ManuscriptChain.BasisInvariance.det_changeBasisPencil
#print axioms ManuscriptChain.BasisInvariance.primitiveNormalization_nonempty
#print axioms ManuscriptChain.BasisInvariance.theorem_2_4_canonical_basis_invariance
#print axioms ManuscriptChain.BasisInvariance.theorem_2_4_constructed_canonical_basis_invariance
#print axioms ManuscriptChain.PoleDiagonalization.poleWeight_ne_zero
#print axioms ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_factorization
#print axioms ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_det_ne_zero
#print axioms ManuscriptChain.PoleDiagonalization.delta_natDegree
#print axioms ManuscriptChain.PoleDiagonalization.theorem_2_5_lagrange_pole_diagonalization
#print axioms ManuscriptChain.BasisInvariance.theorem_2_4_constructed_for_manuscript

#print axioms ManuscriptChain.RealTransfer.polynomial_integer_squeeze
#print axioms ManuscriptChain.RealTransfer.conditional_measure
#print axioms ManuscriptChain.RealTransfer.RationalMeasure.irrational
#print axioms ManuscriptChain.RealTransfer.conditional_irrational
#print axioms ManuscriptChain.RealTransfer.paper_parameter_inequalities

#print axioms ManuscriptChain.Spectral.SymmetricAffinePencil.eval_detPolynomial
#print axioms ManuscriptChain.Spectral.SymmetricAffinePencil.center_nonvanishing_of_positive
#print axioms ManuscriptChain.Real.manuscriptPencil_detPolynomial
#print axioms ManuscriptChain.Real.delta_eval_eq_det_gram
#print axioms ManuscriptChain.Real.delta_nonzero_of_positive

#print axioms ManuscriptChain.Spectral.RootFactorization.complex_root_location
#print axioms ManuscriptChain.Spectral.RootFactorization.eval_ne_zero_of_distance_lt
#print axioms ManuscriptChain.Spectral.det_one_add_smul_of_hermitian
#print axioms ManuscriptChain.Spectral.rootFactorization_nonempty_of_posDef
#print axioms ManuscriptChain.Spectral.theorem_3_1_hyperbolicity_of_posDef
#print axioms ManuscriptChain.General.complex_root_iff
#print axioms ManuscriptChain.General.complex_root_on_boundary
#print axioms ManuscriptChain.General.theorem_3_1_general

#print axioms ManuscriptChain.Moments.quadratic_eq_integral_sq
#print axioms ManuscriptChain.Moments.integral_polynomial_sq_pos
#print axioms ManuscriptChain.Moments.momentMatrix_posDef
#print axioms ManuscriptChain.Real.PositiveMomentRealization.gram_posDef

#print axioms ManuscriptChain.Hyperbolic.summable_exponentialTerm
#print axioms ManuscriptChain.Hyperbolic.density_pos
#print axioms ManuscriptChain.Hyperbolic.measurable_density
#print axioms ManuscriptChain.Hyperbolic.baseMeasure_nonzero
#print axioms ManuscriptChain.Hyperbolic.integral_pow_mul_exp
#print axioms ManuscriptChain.Hyperbolic.integral_tsum_momentTerm
#print axioms ManuscriptChain.Hyperbolic.integrableOn_tsum_momentTerm
#print axioms ManuscriptChain.Hyperbolic.integrableOn_monomial_density
#print axioms ManuscriptChain.Hyperbolic.integral_monomial_density
#print axioms ManuscriptChain.Hyperbolic.integral_monomial_density_eq_monomialMoment

#print axioms ManuscriptChain.Real.zeta_tail_sum
#print axioms ManuscriptChain.Real.zeta_tail_pole_value
#print axioms ManuscriptChain.Hyperbolic.bose_geometric
#print axioms ManuscriptChain.Hyperbolic.integrableOn_bose_tail
#print axioms ManuscriptChain.Hyperbolic.integral_bose_tail_tsum
#print axioms ManuscriptChain.Hyperbolic.integral_bose_tail

#print axioms ManuscriptChain.Hyperbolic.integral_density_div_quadratic
#print axioms ManuscriptChain.Hyperbolic.coth_partial_fractions
#print axioms ManuscriptChain.Hyperbolic.pole_scaled_kernel_split_algebra
#print axioms ManuscriptChain.Hyperbolic.poleIntegralIdentity

#print axioms ManuscriptChain.PartialFractions.tailPoleFactors_pairwise_coprime
#print axioms ManuscriptChain.PartialFractions.kernelNumerator_partial_fraction_exists
#print axioms ManuscriptChain.PartialFractions.data_quotient_eq_div
#print axioms ManuscriptChain.PartialFractions.data_quotient_eq_actual

#print axioms ManuscriptChain.PartialFractions.residueCoeff_eq_formula
#print axioms ManuscriptChain.PartialFractions.residueCoeff_eq_actual
#print axioms ManuscriptChain.PartialFractions.rational_kernel_decomposition

#print axioms ManuscriptChain.Real.D_factorization
#print axioms ManuscriptChain.Tau.pullback_identity_polynomial
#print axioms ManuscriptChain.Tau.tauPolynomial_reflection
#print axioms ManuscriptChain.Tau.tau_difference_pole
#print axioms ManuscriptChain.SimplePole.realize_injective
#print axioms ManuscriptChain.SimplePole.functional_representation_independent
#print axioms ManuscriptChain.ConcreteMoment.weightedMeasure_nonzero
#print axioms ManuscriptChain.ConcreteMoment.momentMeasure_nullSingleton
#print axioms ManuscriptChain.ConcreteMoment.integrableOn_weightedDensity_moment
#print axioms ManuscriptChain.ConcreteMoment.realization
#print axioms ManuscriptChain.Hyperbolic.gram_eq_weighted_integral
#print axioms ManuscriptChain.Hyperbolic.gram_eq_paper_integral
#print axioms ManuscriptChain.REALIZATION
#print axioms ManuscriptChain.GRAM_POSITIVE
#print axioms ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL
#print axioms ManuscriptChain.EXACT_ZERO_FREE_DISK
#print axioms ManuscriptChain.primitivePolynomial_natDegree
#print axioms ManuscriptChain.primitivePolynomial_root_iff
#print axioms ManuscriptChain.primitivePolynomial_exact_zero_free_disk
#print axioms ManuscriptChain.PoleDiagonalization.poleWeight_sign
#print axioms ManuscriptChain.PoleDiagonalization.delta_leadingCoeff_sign
#print axioms ManuscriptChain.BasisInvariance.weightFive_primitive_leadingCoeff_sign
#print axioms ManuscriptChain.ContinuedFractionObstruction.example_delta
#print axioms ManuscriptChain.ContinuedFractionObstruction.positive_center_refutes_printed_fraction
#print axioms ManuscriptChain.ContinuedFractionObstruction.example_reciprocal_hankel_singular

#print axioms ManuscriptChain.Pullback.rationalPullback_coe
#print axioms ManuscriptChain.Pullback.pullback_identity
#print axioms ManuscriptChain.Tau.rationalReflection_coe
#print axioms ManuscriptChain.Tau.rationalFunctional_reflection
#print axioms ManuscriptChain.Mu.realValue_eq_ratFunc_eval
#print axioms ManuscriptChain.Mu.integrableOn_rational_density
#print axioms ManuscriptChain.Mu.integral_rational_density
#print axioms ManuscriptChain.ACTUAL_SPECTRAL_FACTORIZATION
#print axioms ManuscriptChain.ACTUAL_SPECTRAL_ROOTS
#print axioms ManuscriptChain.ACTUAL_OPERATOR_ZERO_FREE_DISK
#print axioms ManuscriptChain.ContinuedFractionObstruction.literal_corollary_3_5_false

#print axioms ManuscriptChain.PoleDiagonalization.lagrangePolynomial_product
#print axioms ManuscriptChain.PoleDiagonalization.lagrangeCoefficientMatrix_eq_inverse
#print axioms ManuscriptChain.PoleDiagonalization.lagrange_changeBasisPencil
#print axioms ManuscriptChain.Tau.tauPolynomial_difference
#print axioms ManuscriptChain.Tau.rationalDifference_coe
#print axioms ManuscriptChain.Tau.rationalFunctional_difference
#print axioms ManuscriptChain.Principal.principal_base_posDef
#print axioms ManuscriptChain.Principal.principal_detPolynomial_eq
#print axioms ManuscriptChain.Principal.rational_principal_roots_real
#print axioms ManuscriptChain.PoleSignCounts.positive_pole_count
#print axioms ManuscriptChain.PoleSignCounts.weightFive_positive_pole_count
#print axioms ManuscriptChain.PoleSignCounts.weightFive_negative_pole_count
#print axioms ManuscriptChain.SpectralInertia.actual_inertia
#print axioms ManuscriptChain.SpectralInertia.actual_root_side_counts

#print axioms ManuscriptChain.SimplePole.denominator_dvd
#print axioms ManuscriptChain.SimplePole.eval_denom_ne_zero
#print axioms ManuscriptChain.Tau.eval_denom_zero_ne_zero
#print axioms ManuscriptChain.Mu.rationalDomain_regular_at_zero
#print axioms ManuscriptChain.SpectralInertia.actual_inertia_formula
#print axioms ManuscriptChain.SpectralInertia.weightFive_actual_inertia
#print axioms ManuscriptChain.SpectralInertia.weightFive_root_side_counts
#print axioms ManuscriptChain.Spectral.reciprocalRootMoment_eq
#print axioms ManuscriptChain.Spectral.evenSpectralMoment_bounds
#print axioms ManuscriptChain.Spectral.reciprocalRootMoment_approximation_bounds
#print axioms ManuscriptChain.ACTUAL_RECIPROCAL_MOMENT_BOUNDS

#print axioms ManuscriptChain.Spectral.reciprocalRootMoment_ratio_tendsto
#print axioms ManuscriptChain.ACTUAL_RECIPROCAL_MOMENT_LIMIT

run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`ManuscriptChain).isPrefixOf name && info.isTheorem then
      checked := checked + 1
      for ax in ← Lean.collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Forbidden dependency {ax} in {name}"
  if checked == 0 then
    throwError "No project theorems found for dependency audit"
  Lean.logInfo m!"GOODWORKFLOWFRONTIER::AXIOM_ALLOWLIST::THEOREMS_CHECKED={checked}"

-- Proposition 4.3: exact ℤ_p, ℚ_p, ℂ_p statements and original integer polynomial.
#print axioms PaperAdvances.Proposition4_3_PadicDisk.PROPOSITION_4_3_INTEGRAL_QPADIC
#print axioms PaperAdvances.Proposition4_3_PadicDisk.PROPOSITION_4_3_INTEGER_QPADIC
#print axioms PaperAdvances.Proposition4_3_IsometricExtension.PROPOSITION_4_3_INTEGRAL_ISOMETRIC_EXTENSION
#print axioms PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGRAL_COMPLEX_PADIC
#print axioms PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGER_COMPLEX_PADIC
#print axioms ManuscriptChain.proposition_4_3_complex_padic_disk
#print axioms ManuscriptChain.primitivePolynomial_complex_padic_disk

#print axioms ManuscriptChain.Tau.reciprocal_even_derivative
#print axioms ManuscriptChain.Tau.poleSpan_normalized_derivative
#print axioms ManuscriptChain.Tau.poleElement_coefficient_eq_analytic
#print axioms ManuscriptChain.Tau.rationalFunctional_difference_analytic_poles

#print axioms ManuscriptChain.Tau.polynomialReal_normalized_derivative
#print axioms ManuscriptChain.Tau.coordinateReal_even_derivative
#print axioms ManuscriptChain.Tau.rationalDomain_coefficient_eq_coordinate_derivative
#print axioms ManuscriptChain.Tau.rationalFunctional_difference_analytic_coordinates

#print axioms ManuscriptChain.Tau.normalized_derivative_rationalDomain
#print axioms ManuscriptChain.Tau.rationalFunctional_difference_analytic

-- Independent integration P05.01: Mellin log moments; source copied from PR #15.
#print axioms ManuscriptChain.UnitLogMoments.image_exp_neg
#print axioms ManuscriptChain.UnitLogMoments.integral_exp_neg_substitution
#print axioms ManuscriptChain.UnitLogMoments.integral_pow_log
#print axioms ManuscriptChain.UnitLogMoments.integrable_pow_log

-- Standalone PR15 Newton/Turan core: audited local integration, not full printed Theorem 3.7.
#print axioms ManuscriptChain.NewtonTuran.Core.turan_eq_zero_iff_multiple_zero
#print axioms ManuscriptChain.NewtonTuran.HigherDerivativeTuran.iterated_turan_nonnegative
#print axioms ManuscriptChain.NewtonTuran.HigherDerivativeTuran.iterated_turan_strict
#print axioms ManuscriptChain.NewtonTuran.NormalizedNewton.coefficient_newton
#print axioms ManuscriptChain.NewtonTuran.ConsecutiveDerivativeZeros.consecutive_taylor_nonvanishing
#print axioms ManuscriptChain.NewtonTuran.StrictNormalizedNewton.coefficient_newton_strict_criterion
#print axioms ManuscriptChain.NewtonTuran.StrictNormalizedNewton.normalized_shifted_newton_strict

-- Independent P03.02 corrected real-s density/moments; full continuous pencil remains open.
#print axioms ManuscriptChain.ContinuousWeight.printedPrefactor_eq
#print axioms ManuscriptChain.ContinuousWeight.density_pos
#print axioms ManuscriptChain.ContinuousWeight.integral_monomial_density
#print axioms ManuscriptChain.ContinuousWeight.weightedDensity_pos
#print axioms ManuscriptChain.ContinuousWeight.weightedMeasure_nonzero
#print axioms ManuscriptChain.ContinuousWeight.momentMeasure_nonzero
#print axioms ManuscriptChain.ContinuousWeight.integral_momentMeasure
#print axioms ManuscriptChain.ContinuousWeight.integrableOn_weightedDensity_moment

-- Theorem 5.4: actual rational integer-pole cancellation and endpoint.
#print axioms ManuscriptChain.Tau.evenPolePair_coe
#print axioms ManuscriptChain.Tau.evenPolePair_cancellation
#print axioms ManuscriptChain.Tau.evenPolePair_one
#print axioms ManuscriptChain.Tau.finite_evenPolePair_cancellation

-- Independent local A-tier support of printed 3.7: exact actual-family declarations.
#print axioms ManuscriptChain.NewtonTuran.Actual.spectral_polynomial_splits
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_primitive_hasDistinctRoots
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_primitive_all_derivative_turan
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_primitive_all_derivative_turan_strict
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_primitive_laguerre
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_centered_consecutive_nonvanishing
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_centered_newton_strict
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_centered_laguerre_strict
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_analytic_turan_nonnegative
#print axioms ManuscriptChain.NewtonTuran.Actual.actual_analytic_turan_strict

#print axioms ManuscriptChain.DualAlgebra.dualSlopeMatrix_eq_CCT
#print axioms ManuscriptChain.DualSpectral.coefficientSlope_posDef
#print axioms ManuscriptChain.Section5DualSpectrum.actual_dual_degree
#print axioms ManuscriptChain.Section5DualSpectrum.actual_dual_zeros_real
#print axioms ManuscriptChain.Beukers.integral_logMonomial
#print axioms ManuscriptChain.Beukers.integral_momentTerm
#print axioms ManuscriptChain.Beukers.integral_density_moment_series
#print axioms ManuscriptChain.Beukers.diagonal_moment
#print axioms ManuscriptChain.Beukers.offdiagonal_moment
#print axioms ManuscriptChain.Beukers.theorem_5_1_exact_moments
#print axioms ManuscriptChain.Beukers.density_strictly_positive_on_square
#print axioms ManuscriptChain.Beukers.density_measurable

#print axioms ManuscriptChain.Beukers.offdiagonal_moment_eq_rat
#print axioms ManuscriptChain.Beukers.offdiagonal_moment_is_rational

-- Conditional all-complex-root separation comparison, isolated from actual ζ5 rate.
#print axioms ManuscriptChain.Spectral.comparisonRadius_pos
#print axioms ManuscriptChain.Section4ComplexComparison.polynomial_comparison
#print axioms ManuscriptChain.Section4ComplexComparison.integer_comparison

-- P04.01: exact conditional rate/index transfer, no specific ζ5 decay assumption discharged.
#print axioms ManuscriptChain.Section4IndexSelection.gridIndex_bounds
#print axioms ManuscriptChain.Section4IndexSelection.gridIndex_tendsto
#print axioms ManuscriptChain.Section4IndexSelection.eventually_radius_budget
#print axioms ManuscriptChain.Section4IndexSelection.eventually_denominator_budget
#print axioms ManuscriptChain.Section4IndexSelection.exists_indexBudget_of_rates
#print axioms ManuscriptChain.Section4IndexSelection.measure_of_rates
#print axioms ManuscriptChain.Section4TransferComplete.spectral_transfer_real_exponent
#print axioms ManuscriptChain.Section4TransferComplete.spectral_transfer_lattice
#print axioms ManuscriptChain.Section4EffectiveBudget.explicit_budgets
#print axioms ManuscriptChain.Section4EffectiveBudget.effective_spectral_measure
#print axioms ManuscriptChain.Section4EffectiveBudget.manuscript_effective_rate_margins

-- P04.02: conditional algebraic-height transfer with exact minimal polynomial wrapper.
#print axioms ManuscriptChain.Section4Resultant.integer_resultant_product
#print axioms ManuscriptChain.Section4Resultant.irreducible_conjugate_product_one_le
#print axioms ManuscriptChain.Section4ConjugateBounds.algebraic_approximation_barrier
#print axioms ManuscriptChain.Section4AlgebraicBudget.eventually_conjugate_budget
#print axioms ManuscriptChain.Section4AlgebraicTransfer.algebraic_transfer_rates
#print axioms ManuscriptChain.Section4AlgebraicLimsup.algebraic_transfer_limsup
#print axioms ManuscriptChain.Section4AlgebraicLattice.proposition_4_2
#print axioms ManuscriptChain.Section4AlgebraicHeight.integerMinimalPolynomial_spec
#print axioms ManuscriptChain.Section4AlgebraicHeight.integerMinimalPolynomial_degree
#print axioms ManuscriptChain.Section4AlgebraicHeight.proposition_4_2_algebraic_numbers

#print axioms ManuscriptChain.Beukers.kreinSix_eq_signed
#print axioms ManuscriptChain.Beukers.integral_momentTerm_eq_kreinSix
#print axioms ManuscriptChain.Beukers.actual_monomial_krein_bilinear
#print axioms ManuscriptChain.Beukers.actual_monomial_krein_quadratic
#print axioms ManuscriptChain.Beukers.polynomialMomentForm_eq_krein
#print axioms ManuscriptChain.Beukers.polynomialMomentForm_quadratic

-- Finite 6.10 potential identity and a corrected rate-direction counterexample.
#print axioms ManuscriptChain.PotentialGap.detPolynomial_coeff_dimension
#print axioms ManuscriptChain.PotentialGap.base_det_mul_whitened_det
#print axioms ManuscriptChain.PotentialGap.abs_coefficient_eq_center_mul_det
#print axioms ManuscriptChain.PotentialGap.log_coefficient_sub_log_center
#print axioms ManuscriptChain.PotentialGap.normalized_log_identity
#print axioms ManuscriptChain.PotentialGap.manuscript_normalized_log_identity
#print axioms ManuscriptChain.PotentialGap.rate_conservation
#print axioms ManuscriptChain.PotentialGap.height_decay_ratio_gt_581
#print axioms ManuscriptChain.PotentialGap.lower_decay_bound_counterexample
#print axioms ManuscriptChain.PotentialGap.evaluation_upper_gives_rate_lower
#print axioms ManuscriptChain.PotentialGap.evaluation_lower_gives_rate_upper

-- Generic ultrametric integer-polynomial disk reused from frozen PR15.
#print axioms ManuscriptChain.Ultrametric.norm_eval_le_one
#print axioms ManuscriptChain.Ultrametric.norm_eval_sub_le
#print axioms ManuscriptChain.Ultrametric.norm_eval_eq_of_mem_disk
#print axioms ManuscriptChain.Ultrametric.eval_ne_zero_of_mem_disk
#print axioms ManuscriptChain.Ultrametric.padicComplex_zero_free_disk

-- P03.04: actual admissible degree-loss counterexample; printed full-rank claim is false.
#print axioms ManuscriptChain.PrincipalDegreeLoss.example_admissible
#print axioms ManuscriptChain.PrincipalDegreeLoss.first_slope_zero
#print axioms ManuscriptChain.PrincipalDegreeLoss.principal_direction_zero
#print axioms ManuscriptChain.PrincipalDegreeLoss.principal_polynomial_constant
#print axioms ManuscriptChain.PrincipalDegreeLoss.first_principal_has_no_complex_roots
#print axioms ManuscriptChain.PrincipalDegreeLoss.literal_all_principal_roots_claim_false
