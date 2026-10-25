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
