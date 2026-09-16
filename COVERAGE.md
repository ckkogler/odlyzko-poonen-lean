# Mathematical coverage

This index records the complete source-result correspondence and every authored
proof declaration. All names are in `OdlyzkoPoonen`. The mathematical development
and official audits cover 672 proved statements and 82 definitions in 182 modules.
All 20 principal claims passed actual independent comparison and both kernel
replays. Fresh standalone verification remains pending.

## Independently compared claims

[Challenge.lean](Challenge.lean) gives the ordinary-language statements and explicit
probability model. [comparator.json](comparator.json) selects all 20 declarations
below; [Solution.lean](Solution.lean) imports the complete proved library.

| Claim | Declaration and proof module |
| --- | --- |
| Model: the sampled family consists exactly of monic endpoint-one binary polynomials of degree m+1. | [`mem_binaryFamily_iff`](OdlyzkoPoonen/Polynomial/BinaryWords.lean) |
| Model: precisely 2^m polynomials have m internal binary coefficients. | [`card_binaryFamily`](OdlyzkoPoonen/Polynomial/BinaryWords.lean) |
| Model: fair independent internal bits give uniform counting on the polynomial family. | [`binaryProbability_eq_count`](OdlyzkoPoonen/Probability/BinaryModel.lean) |
| Theorem 1.1: the probability of irreducibility over the rationals tends to one. | [`odlyzko_poonen_irreducibility`](OdlyzkoPoonen/Asymptotics/Reducibility.lean) |
| Theorem 1.1: reducibility differs from the minus-one root event by O(1/n). | [`binaryProbability_reducible_excess_isBigO`](OdlyzkoPoonen/Asymptotics/Reducibility.lean) |
| Theorem 1.1: one positive constant bounds that nonnegative difference by C/n for all sufficiently large degrees. | [`exists_reducible_probability_excess_bound`](OdlyzkoPoonen/Asymptotics/Reducibility.lean) |
| Theorem 1.1: the reducibility probability is sqrt(2/(pi*n)) with O(1/n) error. | [`binaryProbability_reducible_asymptotic`](OdlyzkoPoonen/Asymptotics/Reducibility.lean) |
| Theorem 1.2: the probability of a genuine modulo-four companion is bounded by the exact degree-split sum, itself at most 8*(3/4)^floor((n-1)/4). | [`mod_four_companion_probability`](OdlyzkoPoonen/ModFour/CompanionProbability.lean) |
| Proposition 2.1: independent uniform degree-d and degree-e endpoint-one polynomials over F2 satisfy the joint nonreciprocity/congruence event with probability at most 2*(3/4)^floor((e-1)/2). | [`factor_pair_congruence_probability`](OdlyzkoPoonen/ModFour/FactorProbability.lean) |
| Lemma 3.1: reversing either monic integer factor preserves binarity and autocorrelation; the two trivial outcomes occur exactly when the corresponding factor is reciprocal. Both factors have constant one. | [`binary_factor_reversal`](OdlyzkoPoonen/Polynomial/FactorReversal.lean) |
| Estimate (3.1): the degree of the gcd of the reduction modulo two and its reciprocal has tail at most 6*2^(-L/2). This includes every natural cutoff L. | [`reciprocal_gcd_probability`](OdlyzkoPoonen/FiniteField/ReciprocalProbability.lean) |
| Estimate (3.2): one absolute positive a and threshold work for every degree and every rationally irreducible noncyclotomic integer factor, with rate exp(-a*n/(log n)^4). No monicity assumption is needed. | [`exists_uniform_noncyclotomic_factor_bound`](OdlyzkoPoonen/Probability/NoncyclotomicFactor.lean) |
| Estimate (3.2), also with ordinary irreducibility in the integer polynomial ring, including all signs and constant cases. | [`exists_uniform_integer_irreducible_noncyclotomic_factor_bound`](OdlyzkoPoonen/Probability/NoncyclotomicFactor.lean) |
| Lemma 3.2, finite bound: a nonconstant reciprocal divisor with no cyclotomic divisor of the original polynomial has probability at most exp(4*L^2-a*n/(log n)^4)+6*2^(-L/2), uniformly in L. | [`exists_unrestricted_reciprocal_finite_bound`](OdlyzkoPoonen/Asymptotics/ReciprocalDivisorNormalization.lean) |
| Lemma 3.2: the same reciprocal/noncyclotomic event has probability O_A(n^(-A)) for every real A>0. | [`binaryProbability_unrestricted_reciprocal_noncyclotomic_isBigO`](OdlyzkoPoonen/Asymptotics/ReciprocalDivisorNormalization.lean) |
| Estimate (3.3): reducibility without any cyclotomic divisor has probability O_A(n^(-A)) for every real A>0. | [`binaryProbability_reducible_noncyclotomic_isBigO`](OdlyzkoPoonen/Asymptotics/ReducibleNoncyclotomic.lean) |
| Estimate (3.4): the probability of a cyclotomic factor of degree at least two is O(1/n). | [`binaryProbability_higher_cyclotomic_isBigO`](OdlyzkoPoonen/Asymptotics/HigherCyclotomic.lean) |
| Exact odd-degree formula: for degree 2r+1 the minus-one root probability is choose(2r,r)/2^(2r), including degree one. | [`binaryProbability_minus_one_odd`](OdlyzkoPoonen/Probability/MinusOne.lean) |
| Exact even-degree formula: for degree 2r the probability is choose(2r-1,r+1)/2^(2r-1), including the zero value at degree two. | [`binaryProbability_minus_one_even`](OdlyzkoPoonen/Probability/MinusOne.lean) |
| Minus-one asymptotic: its probability is sqrt(2/(pi*n)) with the stronger O(n^(-3/2)) error. | [`binaryProbability_minus_one_asymptotic`](OdlyzkoPoonen/Asymptotics/MinusOneAsymptotic.lean) |

## Supporting arguments and source displays

Every supporting argument is proved internally or supplied by pinned Mathlib.
No literature theorem is assumed. The source manuscript supplies the mathematical
targets; historical discussion and bibliographic context are not additional claims.

| Source step | Proved modules |
| --- | --- |
| Binary model and cardinality | Polynomial/BinaryWords, Probability/FiniteUniform and BinaryModel; exact finite uniform law |
| Reversal and autocorrelation | Polynomial/Reversal, Polynomial/Autocorrelation; standard reverse and central coefficient |
| Finite-field endpoint model | Polynomial/Reduction, FiniteField/BinaryFamily, Probability/FiniteFieldModel; exact lift, reversal and uniform pair law |
| Proposition 2.1 | ModFour/FactorProbability; exact independent pair model, constant 2 and floor exponent |
| (2.1) | ModFour/ExposureToggle, Complementation, FiniteField/PairedToggle, Polynomial/OuterAutocorrelation |
| Opposite-pair joint law | Probability/OppositeIndices, OppositeWords; FiniteField/Bits, WordCoefficients, PairedPolynomial, PairSums |
| (2.2) | CoefficientLocality, OuterAgreement, DiscrepancyLocality, PairedUpdate, FiberEstimate |
| Finite averaging | UniformAverage, BitWeights; fiber probabilities and exact (3/4)^m bit average |
| First-asymmetry index and distribution | FirstTrueBit, ReciprocalPairs, FirstAsymmetry, AsymmetryLaw; exact 2^-j, existence/range/uniqueness, both parities |
| Lambda distribution and averaging | InitialCoefficient, Convolution, WordPrefix, PairSumPrefix, ShiftedSlopes, AsymmetryGeometricSum |
| Theorem 1.2 | CompanionFactorization, CompanionReduction, FactorWitnesses, CompanionUnionBound, SplitGeometricBound, CompanionProbability |
| Lemma 3.1 | Polynomial/FactorReversal; full exact statement via algebraic constants |
| Positivity and real-root supporting claims | Polynomial/PositiveRealRoots |
| (3.1) | ReciprocalProbability, ReciprocalTail, ReciprocalDivisorReduction, ReciprocalIntegerDivisors |
| Root and Vieta bounds | Polynomial/RootBound, DivisorCoefficientBound, BoundedMonicFamily, DivisorCount |
| (3.2), cited BV19 Lemma 40 | Probability/NoncyclotomicMonicFactor, NoncyclotomicFactor; uniform fixed-endpoint bound |
| External arithmetic inputs | Quantitative Mahler, controlled separating primes, norm and sparse uniqueness |
| Lemma 3.2 | ReciprocalDivisorCandidates, ReciprocalNoncyclotomicFiniteBound, ReciprocalCutoff, ReciprocalNoncyclotomic |
| (3.3) | Asymptotics/ReducibleNoncyclotomic and GeometricQuotientDecay |
| (3.4), BV19 Lemma 45 / Section 9.2 | CyclotomicResidueBound, CyclotomicRangeSum, CyclotomicCutoff, HigherCyclotomic |
| Exact binomial identities | Probability/BernoulliCount, Polynomial/MinusOneEvaluation, Probability/MinusOne |
| Stirling and parity asymptotic | Asymptotics/MinusOneParity and MinusOneAsymptotic; Analysis/SquareRootComparison |
| Cyclotomic classification and nonnegative excess | Polynomial/CyclotomicDivisors, IntegerRoots, Probability/FiniteEvents, Reducibility/EventBounds |
| Theorem 1.1 | Asymptotics/Reducibility, EventComplement |

The fixed-factor argument uses the proved controlled-prime separation and
quantitative Mahler bound. It does not assert the stronger general versions of
external results. See the arithmetic, linear algebra and analysis modules below.

## Complete declaration index

The following lists include every authored theorem, lemma, definition and
structure. Verification.lean prints all 672 proof statements with their axiom
lists, plus all 82 definitions/structures. File links identify the actual proof.

### [OdlyzkoPoonen.Analysis.AtomScale](OdlyzkoPoonen/Analysis/AtomScale.lean)

Proved declarations: `residue_atom_scale_sq`, `residue_atom_scale_le_cutoff`, `residue_order_count_mul_cube`.

### [OdlyzkoPoonen.Analysis.BoundedDegreeMahlerGap](OdlyzkoPoonen/Analysis/BoundedDegreeMahlerGap.lean)

Proved declarations: `exists_pos_le_on_finite`, `exists_pos_log_mahler_gap_bounded_degree`, `exists_pos_noncyclotomic_log_mahler_gap_bounded_degree`.

### [OdlyzkoPoonen.Analysis.ChebyshevInterval](OdlyzkoPoonen/Analysis/ChebyshevInterval.lean)

Proved declarations: `tendsto_log_div_sqrt_atTop`, `eventually_theta_ge_half_log_two_mul`, `eventually_theta_eight_mul_sub_ge`, `exists_threshold_theta_eight_mul_sub_ge`.

### [OdlyzkoPoonen.Analysis.GeometricQuotientDecay](OdlyzkoPoonen/Analysis/GeometricQuotientDecay.lean)

Proved declarations: `eventually_geometric_quarter_le_exp`, `geometric_quarter_isBigO_rpow`.

### [OdlyzkoPoonen.Analysis.IntegerMahlerMeasure](OdlyzkoPoonen/Analysis/IntegerMahlerMeasure.lean)

Proved declarations: `one_le_norm_leadingCoeff_int_map`, `int_mahlerMeasure_le_of_dvd`, `one_lt_mahlerMeasure_of_no_cyclotomic`, `log_mahlerMeasure_pos_of_no_cyclotomic`.

### [OdlyzkoPoonen.Analysis.LogarithmicDomination](OdlyzkoPoonen/Analysis/LogarithmicDomination.lean)

Proved declarations: `eventually_log_pow_le_nat_div_log_pow`.

### [OdlyzkoPoonen.Analysis.LogarithmicScale](OdlyzkoPoonen/Analysis/LogarithmicScale.lean)

Proved declarations: `log_nat_pow_isLittleO_nat`, `tendsto_log_nat_pow_div_nat`, `exists_threshold_logarithmic_prime_scale`.

### [OdlyzkoPoonen.Analysis.MahlerParameterBudget](OdlyzkoPoonen/Analysis/MahlerParameterBudget.lean)

Proved declarations: `mahler_log_lower_of_parameter_budget`.

### [OdlyzkoPoonen.Analysis.MahlerParameterEstimates](OdlyzkoPoonen/Analysis/MahlerParameterEstimates.lean)

Proved declarations: `mahler_parameter_ceil_bounds`, `mahler_prime_scale_log_lower`, `mahler_prime_card_budget`, `mahler_prime_sum_budget`, `mahler_bad_prime_log_budget`, `mahler_node_log_budget`.

### [OdlyzkoPoonen.Analysis.MahlerRootPowers](OdlyzkoPoonen/Analysis/MahlerRootPowers.lean)

Proved declarations: `max_one_norm_pow`, `prod_max_one_norm_mono`, `roots_pow_le_of_dvd_expand`, `mahlerMeasure_pow_le_of_dvd_expand`.

### [OdlyzkoPoonen.Analysis.PolynomialRootPowers](OdlyzkoPoonen/Analysis/PolynomialRootPowers.lean)

Definitions: `polynomialRootPowers`.

Proved declarations: `polynomialRootPowers_eq_prod_of_splits`, `polynomialRootPowers_eq_prod`, `polynomialRootPowers_leadingCoeff_of_splits`, `polynomialRootPowers_natDegree_of_splits`, `polynomialRootPowers_dvd_pow_of_dvd_comp`, `polynomialRootPowers_mahlerMeasure`, `polynomialRootPowers_map`, `polynomialRootPowers_isRoot`.

### [OdlyzkoPoonen.Analysis.QuantitativeMahlerLargeDegree](OdlyzkoPoonen/Analysis/QuantitativeMahlerLargeDegree.lean)

Proved declarations: `quantitative_mahler_of_large_log_degree`, `exists_threshold_quantitative_mahler_large_degree`.

### [OdlyzkoPoonen.Analysis.ReciprocalCutoff](OdlyzkoPoonen/Analysis/ReciprocalCutoff.lean)

Proved declarations: `eventually_exp_cutoff_cost_le_rpow`, `two_rpow_neg_half_ceil_log_le`, `isBigO_rpow_of_reciprocal_finite_bound`.

### [OdlyzkoPoonen.Analysis.RepeatedRootMahler](OdlyzkoPoonen/Analysis/RepeatedRootMahler.lean)

Proved declarations: `prod_max_norm_root_powers`, `prod_max_norm_eq_mahler_of_factorization`, `prod_max_norm_repeated_root_powers`, `prod_max_norm_option_root_powers`.

### [OdlyzkoPoonen.Analysis.RootPowerMahlerInequality](OdlyzkoPoonen/Analysis/RootPowerMahlerInequality.lean)

Proved declarations: `prime_family_mahler_power_inequality`, `prime_family_mahler_log_inequality`.

### [OdlyzkoPoonen.Analysis.SparseMahlerScale](OdlyzkoPoonen/Analysis/SparseMahlerScale.lean)

Proved declarations: `logarithmic_prime_scale_ge`, `log_lt_prime_mul_log_of_mahler_gap`.

### [OdlyzkoPoonen.Analysis.SquareRootComparison](OdlyzkoPoonen/Analysis/SquareRootComparison.lean)

Proved declarations: `inverse_sqrt_pi_le`, `sqrt_two_div_double`, `sqrt_odd_degree_comparison`, `inverse_three_halves_comparison`, `rpow_neg_three_halves`.

### [OdlyzkoPoonen.Analysis.UniformQuantitativeMahler](OdlyzkoPoonen/Analysis/UniformQuantitativeMahler.lean)

Proved declarations: `exists_uniform_quantitative_log_mahler_bound`.

### [OdlyzkoPoonen.Arithmetic.BinaryLogBounds](OdlyzkoPoonen/Arithmetic/BinaryLogBounds.lean)

Proved declarations: `natLog_two_le_real_log_div`, `nat_pow_le_two_pow_log_multiple`.

### [OdlyzkoPoonen.Arithmetic.GoodRootPowerPrimes](OdlyzkoPoonen/Arithmetic/GoodRootPowerPrimes.lean)

Definitions: `goodRootPowerPrimes`.

Proved declarations: `mem_goodRootPowerPrimes`, `goodRootPowerPrimes_subset`, `sum_log_bad_root_power_primes_le`, `good_root_power_prime_weight_lower`, `card_goodRootPowerPrimes_le`, `sum_goodRootPowerPrimes_le`, `exists_threshold_good_root_power_prime_weight`.

### [OdlyzkoPoonen.Arithmetic.PrimeFamilyBounds](OdlyzkoPoonen/Arithmetic/PrimeFamilyBounds.lean)

Proved declarations: `card_mul_log_lower_le_prime_weight`, `prime_weight_le_card_mul_log_upper`, `sum_primes_le_card_mul_upper`, `prime_weight_le_sixteen_mul`, `card_prime_family_le`.

### [OdlyzkoPoonen.Arithmetic.PrimeIntervalGrowth](OdlyzkoPoonen/Arithmetic/PrimeIntervalGrowth.lean)

Proved declarations: `eventually_exp_le_primeIntervalProduct`, `exists_threshold_exp_le_primeIntervalProduct`, `exists_prime_in_interval_not_dvd_of_log_lt`.

### [OdlyzkoPoonen.Arithmetic.PrimeIntervals](OdlyzkoPoonen/Arithmetic/PrimeIntervals.lean)

Definitions: `primesInInterval`, `primeIntervalProduct`.

Proved declarations: `mem_primesInInterval`, `primeIntervalProduct_pos`, `log_primeIntervalProduct`, `primeIntervalProduct_dvd`, `exists_prime_in_interval_not_dvd`.

### [OdlyzkoPoonen.Arithmetic.PrimitiveRootProducts](OdlyzkoPoonen/Arithmetic/PrimitiveRootProducts.lean)

Proved declarations: `primitiveRoot_mul_of_coprime`.

### [OdlyzkoPoonen.Arithmetic.ResidueClassSize](OdlyzkoPoonen/Arithmetic/ResidueClassSize.lean)

Proved declarations: `card_positive_residue_class_ge`, `card_positive_residue_class_add_one_ge`.

### [OdlyzkoPoonen.Arithmetic.SparsePositions](OdlyzkoPoonen/Arithmetic/SparsePositions.lean)

Proved declarations: `card_sparse_internal_positions`.

### [OdlyzkoPoonen.Arithmetic.SparseQuotientBounds](OdlyzkoPoonen/Arithmetic/SparseQuotientBounds.lean)

Proved declarations: `nat_div_ge_half_real_ratio`, `sparse_quotient_lower`, `half_pow_sparse_quotient_le_exp`.

### [OdlyzkoPoonen.Arithmetic.TotientOrder](OdlyzkoPoonen/Arithmetic/TotientOrder.lean)

Proved declarations: `coprime_odd_or_odd`, `order_le_totient_sq_with_odd`, `order_le_two_totient_sq`, `odd_order_le_totient_sq`.

### [OdlyzkoPoonen.Asymptotics.CentralBinomial](OdlyzkoPoonen/Asymptotics/CentralBinomial.lean)

Definitions: `centralBinomialMass`.

Proved declarations: `centralBinomialMass_pos`, `centralBinomialMass_eq_choose`, `centralBinomialMass_wallis_identity`, `centralBinomialMass_sq_lower`, `centralBinomialMass_sq_upper_aux`, `centralBinomialMass_sq_upper`, `centralBinomialMass_le_sqrt`, `centralBinomialMass_abs_sub_sqrt_le`.

### [OdlyzkoPoonen.Asymptotics.CyclotomicCutoff](OdlyzkoPoonen/Asymptotics/CyclotomicCutoff.lean)

Definitions: `cyclotomicDegreeCutoff`.

Proved declarations: `cyclotomicDegreeCutoff_pos`, `pow_eight_le_two_pow_cyclotomicDegreeCutoff`, `cyclotomicDegreeCutoff_le_log`, `cyclotomicDegreeCutoff_isBigO_log`, `log_nat_pow_isLittleO_sqrt`, `cyclotomicDegreeCutoff_pow_isLittleO_sqrt`, `tendsto_cyclotomicDegreeCutoff_pow_div_sqrt`, `eventually_cyclotomic_cutoff_scale_le_one`.

### [OdlyzkoPoonen.Asymptotics.HigherCyclotomic](OdlyzkoPoonen/Asymptotics/HigherCyclotomic.lean)

Proved declarations: `cyclotomic_cutoff_tail_le`, `eventually_binaryProbability_higher_cyclotomic_le`, `exists_threshold_higher_cyclotomic_bound`, `binaryProbability_higher_cyclotomic_isBigO`, `tendsto_higher_cyclotomic_probability`.

### [OdlyzkoPoonen.Asymptotics.MinusOneAsymptotic](OdlyzkoPoonen/Asymptotics/MinusOneAsymptotic.lean)

Proved declarations: `binaryProbability_minus_one_error_bound`, `binaryProbability_minus_one_error_rpow`, `binaryProbability_minus_one_asymptotic`, `tendsto_minus_one_leading_term`, `tendsto_minus_one_probability`.

### [OdlyzkoPoonen.Asymptotics.MinusOneMass](OdlyzkoPoonen/Asymptotics/MinusOneMass.lean)

Proved declarations: `adjacent_even_choose_identity`, `binaryProbability_minus_one_odd_eq_central`, `binaryProbability_minus_one_even_eq_central`.

### [OdlyzkoPoonen.Asymptotics.MinusOneParity](OdlyzkoPoonen/Asymptotics/MinusOneParity.lean)

Proved declarations: `binaryProbability_minus_one_even_error`, `binaryProbability_minus_one_odd_error`.

### [OdlyzkoPoonen.Asymptotics.ReciprocalDivisorNormalization](OdlyzkoPoonen/Asymptotics/ReciprocalDivisorNormalization.lean)

Proved declarations: `exists_unrestricted_reciprocal_finite_bound`, `binaryProbability_unrestricted_reciprocal_noncyclotomic_isBigO`.

### [OdlyzkoPoonen.Asymptotics.ReciprocalNoncyclotomic](OdlyzkoPoonen/Asymptotics/ReciprocalNoncyclotomic.lean)

Proved declarations: `binaryProbability_reciprocal_noncyclotomic_isBigO`.

### [OdlyzkoPoonen.Asymptotics.Reducibility](OdlyzkoPoonen/Asymptotics/Reducibility.lean)

Proved declarations: `binaryProbability_reducible_excess_isBigO`, `exists_reducible_probability_excess_bound`, `nat_rpow_neg_three_halves_isBigO_inverse`, `binaryProbability_reducible_asymptotic`, `tendsto_reducible_probability`, `odlyzko_poonen_irreducibility`.

### [OdlyzkoPoonen.Asymptotics.ReducibleNoncyclotomic](OdlyzkoPoonen/Asymptotics/ReducibleNoncyclotomic.lean)

Proved declarations: `binaryProbability_companion_isBigO`, `binaryProbability_reducible_noncyclotomic_isBigO`.

### [OdlyzkoPoonen.FiniteField.AutocorrelationFactors](OdlyzkoPoonen/FiniteField/AutocorrelationFactors.lean)

Proved declarations: `cancel_common_autocorrelation_factor`, `coprime_equal_autocorrelation_reverse`.

### [OdlyzkoPoonen.FiniteField.BinaryFamily](OdlyzkoPoonen/FiniteField/BinaryFamily.lean)

Definitions: `HasF2Endpoints`, `f2WordPolynomial`, `f2Family`.

Proved declarations: `HasBinaryEndpoints.reduce`, `HasF2Endpoints.lift`, `zeroOneLift_endpoints_iff`, `HasF2Endpoints.reverse`, `HasF2Endpoints.mul`, `f2WordPolynomial_endpoints`, `f2WordPolynomial_injective`, `exists_f2WordPolynomial_eq`, `mem_f2Family_iff`, `card_f2Family`.

### [OdlyzkoPoonen.FiniteField.BitTests](OdlyzkoPoonen/FiniteField/BitTests.lean)

Proved declarations: `bitToF2_eq_zero_iff`, `bitToF2_eq_one_iff`.

### [OdlyzkoPoonen.FiniteField.Bits](OdlyzkoPoonen/FiniteField/Bits.lean)

Definitions: `bitToF2`, `f2ToBit`, `bitF2Equiv`.

Proved declarations: `bitToF2_eq_int_cast`, `f2ToBit_bitToF2`, `bitToF2_f2ToBit`, `bitToF2_xor`, `bitToF2_not`, `f2ToBit_add_one`, `f2ToBit_eq_false_iff`, `f2ToBit_eq_true_iff`.

### [OdlyzkoPoonen.FiniteField.CompanionFactorization](OdlyzkoPoonen/FiniteField/CompanionFactorization.lean)

Proved declarations: `equal_autocorrelation_factorization`, `nontrivial_companion_factorization`, `ordered_companion_factorization`.

### [OdlyzkoPoonen.FiniteField.Convolution](OdlyzkoPoonen/FiniteField/Convolution.lean)

Definitions: `coefficientConvolution`, `coefficientConvolutionCorrection`.

Proved declarations: `f2ToBit_add`, `coefficientConvolutionCorrection_dependsOnEarlier`, `coefficientConvolution_eq_triangular`, `coefficientConvolution_bijective`, `uniformAverage_coefficientConvolution_half_weight`.

### [OdlyzkoPoonen.FiniteField.DivisorCounting](OdlyzkoPoonen/FiniteField/DivisorCounting.lean)

Proved declarations: `HasF2Endpoints.not_dvd_of_degree_lt`, `HasF2Endpoints.exists_endpoint_quotient`, `card_endpoint_multiples_le`, `f2Probability_divisible_eq_zero`, `f2Probability_divisible_le`.

### [OdlyzkoPoonen.FiniteField.EndpointFamily](OdlyzkoPoonen/FiniteField/EndpointFamily.lean)

Definitions: `f2EndpointFamily`.

Proved declarations: `mem_f2EndpointFamily_iff`, `card_f2EndpointFamily`, `f2EndpointFamily_nonempty`, `card_f2EndpointFamily_le`, `card_reciprocal_f2EndpointFamily`.

### [OdlyzkoPoonen.FiniteField.FactorEndpoints](OdlyzkoPoonen/FiniteField/FactorEndpoints.lean)

Proved declarations: `f2_eq_one_of_ne_zero`, `f2_monic_of_ne_zero`, `f2_endpoints_of_constant`, `HasF2Endpoints.factor_endpoints`, `HasF2Endpoints.reverse_reverse`, `HasF2Endpoints.eq_one_of_degree_zero`, `HasF2Endpoints.degree_pos_of_nonreciprocal`.

### [OdlyzkoPoonen.FiniteField.FirstAsymmetry](OdlyzkoPoonen/FiniteField/FirstAsymmetry.lean)

Definitions: `FirstAsymmetryAt`.

Proved declarations: `firstAsymmetryAt_paired_iff`, `FirstAsymmetryAt.unique`, `FirstAsymmetryAt.ne_reverse`, `HasF2Endpoints.exists_firstAsymmetry`.

### [OdlyzkoPoonen.FiniteField.GcdFactors](OdlyzkoPoonen/FiniteField/GcdFactors.lean)

Proved declarations: `exists_coprime_endpoint_factors`.

### [OdlyzkoPoonen.FiniteField.InteriorPolynomial](OdlyzkoPoonen/FiniteField/InteriorPolynomial.lean)

Definitions: `f2InteriorPolynomial`.

Proved declarations: `coeff_f2InteriorPolynomial`, `coeff_f2InteriorPolynomial_outside`, `coeff_f2InteriorPolynomial_zero`, `f2InteriorPolynomial_prefix`.

### [OdlyzkoPoonen.FiniteField.OuterAgreement](OdlyzkoPoonen/FiniteField/OuterAgreement.lean)

Proved declarations: `AgreeOnOuter.reverse`, `AgreeOnOuter.mul_left`, `AgreeOnOuter.zeroOneLift`.

### [OdlyzkoPoonen.FiniteField.PairSumPrefix](OdlyzkoPoonen/FiniteField/PairSumPrefix.lean)

Proved declarations: `coeff_pairSumPolynomial_zero`, `pairSumPolynomial_prefix`.

### [OdlyzkoPoonen.FiniteField.PairSums](OdlyzkoPoonen/FiniteField/PairSums.lean)

Definitions: `pairSumPolynomial`.

Proved declarations: `paired_sum_reverse_eq`, `paired_sum_reverse_eq_pairSumPolynomial`, `coeff_pairSumPolynomial_lower`, `pairSumPolynomial_injective`.

### [OdlyzkoPoonen.FiniteField.PairedPolynomial](OdlyzkoPoonen/FiniteField/PairedPolynomial.lean)

Definitions: `pairedPolynomial`.

Proved declarations: `pairedPolynomial_endpoints`, `coeff_pairedPolynomial_lower`, `coeff_pairedPolynomial_upper`, `coeff_pairedPolynomial_center`, `coeff_paired_sum_reverse_lower`, `coeff_add_reverse_opposite`, `coeff_paired_sum_reverse_upper`, `coeff_paired_sum_reverse_center`, `f2Probability_eq_paired_average`.

### [OdlyzkoPoonen.FiniteField.PairedToggle](OdlyzkoPoonen/FiniteField/PairedToggle.lean)

Definitions: `togglePair`.

Proved declarations: `HasF2Endpoints.togglePair`, `reverse_togglePair`, `coeff_mul_togglePair_before`, `coeff_mul_togglePair_at`, `coeff_mul_togglePair_opposite`, `coeff_mul_togglePair_opposite_before`, `togglePair_togglePair`, `togglePair_add_reverse`.

### [OdlyzkoPoonen.FiniteField.PairedUpdate](OdlyzkoPoonen/FiniteField/PairedUpdate.lean)

Proved declarations: `pairedPolynomial_update`.

### [OdlyzkoPoonen.FiniteField.ReciprocalGcd](OdlyzkoPoonen/FiniteField/ReciprocalGcd.lean)

Proved declarations: `f2_reverse_dvd_reverse`, `HasF2Endpoints.divisor_endpoints`, `HasF2Endpoints.gcd_reverse_endpoints`, `HasF2Endpoints.gcd_reverse_degree_le`, `HasF2Endpoints.gcd_reverse_reciprocal`.

### [OdlyzkoPoonen.FiniteField.ReciprocalPairs](OdlyzkoPoonen/FiniteField/ReciprocalPairs.lean)

Proved declarations: `HasF2Endpoints.reverse_eq_iff_lower`, `pairedPolynomial_reverse_eq_iff`.

### [OdlyzkoPoonen.FiniteField.ReciprocalProbability](OdlyzkoPoonen/FiniteField/ReciprocalProbability.lean)

Proved declarations: `f2Probability_gcd_degree_le`, `reciprocal_gcd_probability`.

### [OdlyzkoPoonen.FiniteField.ReciprocalUnionBound](OdlyzkoPoonen/FiniteField/ReciprocalUnionBound.lean)

Definitions: `HasReciprocalF2Divisor`.

Proved declarations: `hasReciprocalF2Divisor_iff_mem`, `f2Probability_reciprocal_divisor_le`, `HasF2Endpoints.exists_reciprocal_divisor_of_gcd_degree`, `f2Probability_gcd_degree_le_sum`.

### [OdlyzkoPoonen.FiniteField.WordCoefficients](OdlyzkoPoonen/FiniteField/WordCoefficients.lean)

Proved declarations: `HasF2Endpoints.coeff_degree`, `HasF2Endpoints.coeff_eq_zero_above`, `coeff_f2WordPolynomial_internal`, `f2WordPolynomial_ext`, `reverse_f2WordPolynomial`.

### [OdlyzkoPoonen.LinearAlgebra.ConfluentIntegerLowerBound](OdlyzkoPoonen/LinearAlgebra/ConfluentIntegerLowerBound.lean)

Proved declarations: `norm_resultant_comm`, `norm_det_confluent_ge_cross_product`.

### [OdlyzkoPoonen.LinearAlgebra.ConfluentResultants](OdlyzkoPoonen/LinearAlgebra/ConfluentResultants.lean)

Proved declarations: `norm_det_confluent_eq_resultant_product`.

### [OdlyzkoPoonen.LinearAlgebra.ConfluentVandermonde](OdlyzkoPoonen/LinearAlgebra/ConfluentVandermonde.lean)

Definitions: `rootPrefixPolynomial`, `rootPrefixMultiplicity`, `confluentVandermonde`.

Proved declarations: `rootPrefixPolynomial_monic`, `rootPrefixPolynomial_natDegree`, `rootPrefixMultiplicity_le`, `rootPrefixMultiplicity_lt_later_count`, `hasseDeriv_eval_eq_sum_fin`, `confluentVandermonde_mul_coefficients`, `confluentVandermonde_newton_lowerTriangular`, `confluentVandermonde_newton_diagonal`, `det_confluentVandermonde`, `det_confluentVandermonde_ne_zero`.

### [OdlyzkoPoonen.LinearAlgebra.ConfluentVandermondeBound](OdlyzkoPoonen/LinearAlgebra/ConfluentVandermondeBound.lean)

Proved declarations: `norm_confluentVandermonde_entry_le`, `norm_det_confluentVandermonde_le`, `norm_det_confluentVandermonde_le_power`.

### [OdlyzkoPoonen.LinearAlgebra.ConfluentVandermondeProducts](OdlyzkoPoonen/LinearAlgebra/ConfluentVandermondeProducts.lean)

Proved declarations: `norm_det_confluentVandermonde_sq`, `norm_det_confluentVandermonde_sq_equiv`.

### [OdlyzkoPoonen.LinearAlgebra.DeterminantNormBound](OdlyzkoPoonen/LinearAlgebra/DeterminantNormBound.lean)

Proved declarations: `norm_det_le_factorial_mul_prod`.

### [OdlyzkoPoonen.LinearAlgebra.RepeatedProducts](OdlyzkoPoonen/LinearAlgebra/RepeatedProducts.lean)

Proved declarations: `prod_repeated_pairs`.

### [OdlyzkoPoonen.LinearAlgebra.RepeatedRootCounts](OdlyzkoPoonen/LinearAlgebra/RepeatedRootCounts.lean)

Proved declarations: `card_repeated_family`, `repeated_root_fiber_count`, `rootPrefixMultiplicity_repeated_le`, `sum_rootPrefixMultiplicity_repeated_le`, `card_repeated_option_family`.

### [OdlyzkoPoonen.LinearAlgebra.RootPowerDeterminantLowerBound](OdlyzkoPoonen/LinearAlgebra/RootPowerDeterminantLowerBound.lean)

Proved declarations: `root_power_determinant_lower_bound`.

### [OdlyzkoPoonen.LinearAlgebra.RootPowerDeterminantUpperBound](OdlyzkoPoonen/LinearAlgebra/RootPowerDeterminantUpperBound.lean)

Proved declarations: `root_power_determinant_upper_bound`.

### [OdlyzkoPoonen.LinearAlgebra.SymmetricProductBounds](OdlyzkoPoonen/LinearAlgebra/SymmetricProductBounds.lean)

Proved declarations: `option_symmetric_prod_lower`.

### [OdlyzkoPoonen.LinearAlgebra.SymmetricProducts](OdlyzkoPoonen/LinearAlgebra/SymmetricProducts.lean)

Proved declarations: `prod_symmetric_eq_lower_sq`.

### [OdlyzkoPoonen.ModFour.CompanionProbability](OdlyzkoPoonen/ModFour/CompanionProbability.lean)

Proved declarations: `companion_split_sum_eq_Icc`, `mod_four_companion_probability`, `mod_four_companion_probability_le`.

### [OdlyzkoPoonen.ModFour.CompanionReduction](OdlyzkoPoonen/ModFour/CompanionReduction.lean)

Definitions: `HasModFourCompanion`.

Proved declarations: `CongruentMod.of_dvd`, `binary_autocorrelations_reduce_eq`, `HasModFourCompanion.factorization`.

### [OdlyzkoPoonen.ModFour.CompanionUnionBound](OdlyzkoPoonen/ModFour/CompanionUnionBound.lean)

Proved declarations: `HasModFourCompanion.exists_factor_witness`, `binaryProbability_companion_le_split_sum`.

### [OdlyzkoPoonen.ModFour.Complementation](OdlyzkoPoonen/ModFour/Complementation.lean)

Proved declarations: `halfCoefficientDifference_change`, `halfAutocorrelation_change_of_complementation`.

### [OdlyzkoPoonen.ModFour.DiscrepancyLocality](OdlyzkoPoonen/ModFour/DiscrepancyLocality.lean)

Definitions: `pairedDiscrepancy`.

Proved declarations: `autocorrelationDiscrepancy_eq_of_outer`, `pairedPolynomial_agreeOnOuter`, `pairedDiscrepancy_eq_of_prefix`, `pairedDiscrepancy_dependsOnPrefix`, `pairedDiscrepancy_center_independent`.

### [OdlyzkoPoonen.ModFour.ExposureToggle](OdlyzkoPoonen/ModFour/ExposureToggle.lean)

Proved declarations: `int_val_add_one_zmod_two`, `asymmetry_product_coeff`, `autocorrelationDiscrepancy_togglePair`.

### [OdlyzkoPoonen.ModFour.FactorProbability](OdlyzkoPoonen/ModFour/FactorProbability.lean)

Proved declarations: `f2PairProbability_first_asymmetry_contribution`, `f2PairProbability_factor_congruence_le`, `factor_pair_congruence_probability`.

### [OdlyzkoPoonen.ModFour.FactorWitnesses](OdlyzkoPoonen/ModFour/FactorWitnesses.lean)

Definitions: `HasFactorWitness`.

Proved declarations: `hasFactorWitness_iff_words`, `factor_pair_word_card_ratio`, `binaryProbability_factor_witness_le`.

### [OdlyzkoPoonen.ModFour.FiberEstimate](OdlyzkoPoonen/ModFour/FiberEstimate.lean)

Definitions: `activeDiscrepancyIndices`.

Proved declarations: `pairedDiscrepancy_togglesOn`, `paired_discrepancies_zero_probability_le`, `paired_discrepancies_zero_fiber_probability_le`, `paired_factor_congruence_probability_le`, `f2_factor_congruence_probability_le_average`.

### [OdlyzkoPoonen.ModFour.Parity](OdlyzkoPoonen/ModFour/Parity.lean)

Definitions: `halfCoefficientDifference`, `autocorrelationDiscrepancy`.

Proved declarations: `lifted_factor_autocorrelation_congruent_two`, `lifted_factor_autocorrelation_even`, `four_dvd_iff_two_dvd_half`, `halfCoefficientDifference_eq_zero_iff`, `congruent_four_iff_half_differences_zero`, `lifted_factor_congruent_four_iff`.

### [OdlyzkoPoonen.ModFour.ShiftedSlopes](OdlyzkoPoonen/ModFour/ShiftedSlopes.lean)

Definitions: `exposureSlopeWord`.

Proved declarations: `activeDiscrepancyIndices_card`, `exposureSlopeWord_zero_before`, `exposureSlopeWord_shifted`, `uniformAverage_active_discrepancy_weight`, `f2_factor_congruence_probability_le_of_firstAsymmetry`.

### [OdlyzkoPoonen.ModFour.SplitGeometricBound](OdlyzkoPoonen/ModFour/SplitGeometricBound.lean)

Proved declarations: `sum_range_floor_half_even`, `sum_three_quarters_range`, `sum_floor_half_three_quarters_le_eight`, `companion_split_exponent_lower`, `companion_split_exponent_reversed`, `companion_split_exponent_fiber_card_le_two`, `companion_split_sum_le_eight`.

### [OdlyzkoPoonen.Polynomial.Autocorrelation](OdlyzkoPoonen/Polynomial/Autocorrelation.lean)

Proved declarations: `coeff_autocorrelation_middle`, `eval_one_eq_sum_coeff`, `int_mul_sub_one_nonneg`, `isBinary_of_sum_sq_eq_sum`, `IsBinary.of_autocorrelation_eq`.

### [OdlyzkoPoonen.Polynomial.Binary](OdlyzkoPoonen/Polynomial/Binary.lean)

Definitions: `IsBinary`, `HasBinaryEndpoints`.

Proved declarations: `IsBinary.coeff_nonneg`, `IsBinary.coeff_le_one`, `IsBinary.coeff_sq`, `isBinary_iff_coeff_sq`, `HasBinaryEndpoints.ne_zero`, `HasBinaryEndpoints.coeff_degree`, `HasBinaryEndpoints.coeff_eq_zero_above`, `HasBinaryEndpoints.natTrailingDegree`.

### [OdlyzkoPoonen.Polynomial.BinaryDifference](OdlyzkoPoonen/Polynomial/BinaryDifference.lean)

Proved declarations: `IsBinary.norm_coeff_sub_le_one`, `coeff_wordPolynomial_sub_outside`, `support_wordPolynomial_sub_map_subset`, `mahlerMeasure_wordPolynomial_sub_le`.

### [OdlyzkoPoonen.Polynomial.BinaryWords](OdlyzkoPoonen/Polynomial/BinaryWords.lean)

Definitions: `bitValue`, `interiorPolynomial`, `wordPolynomial`, `binaryFamily`.

Proved declarations: `bitValue_binary`, `bitValue_injective`, `coeff_interiorPolynomial`, `coeff_interiorPolynomial_outside`, `coeff_wordPolynomial_zero`, `coeff_wordPolynomial_top`, `coeff_wordPolynomial_internal`, `coeff_wordPolynomial_above`, `wordPolynomial_injective`, `natDegree_wordPolynomial`, `wordPolynomial_endpoints`, `exists_wordPolynomial_eq`, `mem_binaryFamily_iff`, `card_binaryFamily`.

### [OdlyzkoPoonen.Polynomial.BoundedMonicFamily](OdlyzkoPoonen/Polynomial/BoundedMonicFamily.lean)

Definitions: `monicPolynomialOfCoefficients`, `boundedMonicFamily`.

Proved declarations: `monic_eq_polynomialOfCoefficients`, `card_bounded_integer_interval`, `card_boundedMonicFamily_le`, `mem_boundedMonicFamily_of_coeff_bound`, `HasBinaryEndpoints.monic_divisor_mem_boundedFamily`.

### [OdlyzkoPoonen.Polynomial.CoefficientLocality](OdlyzkoPoonen/Polynomial/CoefficientLocality.lean)

Definitions: `AgreeOnOuter`.

Proved declarations: `AgreeOnOuter.mono`, `coeff_mul_right_eq_of_prefix`, `AgreeOnOuter.autocorrelation`.

### [OdlyzkoPoonen.Polynomial.ComplexConjugatePowers](OdlyzkoPoonen/Polynomial/ComplexConjugatePowers.lean)

Proved declarations: `eq_exponents_of_noncyclotomic_complex_root_powers`.

### [OdlyzkoPoonen.Polynomial.ComplexRootPowerPrime](OdlyzkoPoonen/Polynomial/ComplexRootPowerPrime.lean)

Proved declarations: `exists_prime_separating_complex_roots_of_log_lt`, `exists_prime_separating_integer_polynomial_roots_of_log_lt`.

### [OdlyzkoPoonen.Polynomial.ConjugatePowers](OdlyzkoPoonen/Polynomial/ConjugatePowers.lean)

Proved declarations: `pow_injective_of_no_positive_power_eq_one`, `algEquiv_iterated_power_relation`, `exists_positive_algEquiv_power_fix_root`, `eq_exponents_of_periodic_algEquiv_power_relation`, `eq_exponents_of_conjugate_root_powers`.

### [OdlyzkoPoonen.Polynomial.ContractedBinaryDifference](OdlyzkoPoonen/Polynomial/ContractedBinaryDifference.lean)

Proved declarations: `norm_coeff_contract_word_difference_le_one`, `support_contract_word_difference_map_subset`, `mahlerMeasure_contract_word_difference_le`.

### [OdlyzkoPoonen.Polynomial.CyclotomicDivisors](OdlyzkoPoonen/Polynomial/CyclotomicDivisors.lean)

Definitions: `HasCyclotomicDivisor`, `HasHigherCyclotomicDivisor`.

Proved declarations: `HasCyclotomicDivisor.of_dvd`, `HasHigherCyclotomicDivisor.hasCyclotomicDivisor`, `cyclotomic_dvd_iff_rational`, `HasBinaryEndpoints.eval_int_one_pos`, `HasBinaryEndpoints.not_cyclotomic_one_dvd`, `cyclotomic_two_dvd_iff_minus_one`, `HasBinaryEndpoints.cyclotomic_alternative`, `HasBinaryEndpoints.hasCyclotomicDivisor_iff`.

### [OdlyzkoPoonen.Polynomial.DivisorCoefficientBound](OdlyzkoPoonen/Polynomial/DivisorCoefficientBound.lean)

Proved declarations: `norm_coeff_mul_X_sub_C_le`, `norm_coeff_prod_X_sub_C_le`, `monic_coeff_norm_le_of_roots_le_two`, `HasBinaryEndpoints.monic_divisor_coeff_abs_le`.

### [OdlyzkoPoonen.Polynomial.DivisorCoefficientUniqueness](OdlyzkoPoonen/Polynomial/DivisorCoefficientUniqueness.lean)

Proved declarations: `eq_of_dvd_of_high_coefficients_eq`.

### [OdlyzkoPoonen.Polynomial.DivisorCount](OdlyzkoPoonen/Polynomial/DivisorCount.lean)

Definitions: `smallDivisorCandidates`.

Proved declarations: `bounded_coefficient_choices_le_three_pow`, `divisor_count_summand_le_exp`, `sum_divisor_counts_le_exp`, `HasBinaryEndpoints.monic_divisor_mem_candidates`, `card_smallDivisorCandidates_le_sum`, `card_smallDivisorCandidates_le_exp`.

### [OdlyzkoPoonen.Polynomial.FactorReversal](OdlyzkoPoonen/Polynomial/FactorReversal.lean)

Proved declarations: `eval_one_reverse`, `IsBinary.factor_reverse`, `HasBinaryEndpoints.factor_constants`, `HasBinaryEndpoints.factor_reverse`, `factor_reverse_eq_iff`, `factor_reverse_eq_reverse_iff`, `binary_factor_reversal`.

### [OdlyzkoPoonen.Polynomial.FrobeniusCongruence](OdlyzkoPoonen/Polynomial/FrobeniusCongruence.lean)

Proved declarations: `comp_X_pow_eq_pow_zmod`, `prime_C_dvd_comp_X_pow_sub_pow`.

### [OdlyzkoPoonen.Polynomial.GaloisRoots](OdlyzkoPoonen/Polynomial/GaloisRoots.lean)

Proved declarations: `root_ne_zero_of_constant_ne_zero`, `exists_algEquiv_map_root`, `algEquiv_map_mem_rootSet`, `exists_algEquiv_map_primitiveRoot`, `rootSet_nonempty_of_splits_of_irreducible`.

### [OdlyzkoPoonen.Polynomial.InitialCoefficient](OdlyzkoPoonen/Polynomial/InitialCoefficient.lean)

Proved declarations: `exists_X_pow_factor_of_initial_one`, `coeff_mul_zero_through_initial`, `coeff_mul_after_X_pow_factor`, `coeff_mul_constant_one`.

### [OdlyzkoPoonen.Polynomial.IntegerResultantBounds](OdlyzkoPoonen/Polynomial/IntegerResultantBounds.lean)

Proved declarations: `nat_le_norm_intCast_of_dvd`, `one_le_norm_resultant_int`, `prime_pow_degree_le_norm_rootPower_resultant`.

### [OdlyzkoPoonen.Polynomial.IntegerRootProducts](OdlyzkoPoonen/Polynomial/IntegerRootProducts.lean)

Proved declarations: `one_le_norm_derivative_resultant_of_integer_root_family`, `root_families_disjoint_of_isCoprime`.

### [OdlyzkoPoonen.Polynomial.IntegerRoots](OdlyzkoPoonen/Polynomial/IntegerRoots.lean)

Proved declarations: `monic_reducibleOverRat_of_integer_root`, `HasBinaryEndpoints.reducible_of_minus_one`.

### [OdlyzkoPoonen.Polynomial.LogarithmicRootPowerPrime](OdlyzkoPoonen/Polynomial/LogarithmicRootPowerPrime.lean)

Proved declarations: `exists_uniform_logarithmic_root_power_prime`.

### [OdlyzkoPoonen.Polynomial.MinusOneEvaluation](OdlyzkoPoonen/Polynomial/MinusOneEvaluation.lean)

Definitions: `alternatingComplement`.

Proved declarations: `alternatingComplement_involutive`, `alternatingComplement_bijective`, `sum_bitValue_eq_trueBitCount`, `sum_odd_position_indicators`, `signed_bitValue`, `eval_wordPolynomial_minus_one`.

### [OdlyzkoPoonen.Polynomial.MonicDivisorSign](OdlyzkoPoonen/Polynomial/MonicDivisorSign.lean)

Proved declarations: `monic_or_neg_monic_of_dvd_monic`, `irreducible_map_rat_of_dvd_monic`.

### [OdlyzkoPoonen.Polynomial.MonicIrreducibleDivisor](OdlyzkoPoonen/Polynomial/MonicIrreducibleDivisor.lean)

Proved declarations: `exists_monic_rational_irreducible_divisor`.

### [OdlyzkoPoonen.Polynomial.MonicReduction](OdlyzkoPoonen/Polynomial/MonicReduction.lean)

Proved declarations: `monic_reduce_natDegree`, `monic_reduce_reverse`, `reducePolynomial_dvd`.

### [OdlyzkoPoonen.Polynomial.NoncyclotomicRoots](OdlyzkoPoonen/Polynomial/NoncyclotomicRoots.lean)

Proved declarations: `root_pow_ne_one_of_no_cyclotomic`, `eq_exponents_of_noncyclotomic_root_powers`.

### [OdlyzkoPoonen.Polynomial.OuterAutocorrelation](OdlyzkoPoonen/Polynomial/OuterAutocorrelation.lean)

Proved declarations: `coeff_autocorrelation_le`, `HasBinaryEndpoints.coeff_autocorrelation_outer`, `HasBinaryEndpoints.autocorrelation_outer_difference`.

### [OdlyzkoPoonen.Polynomial.PositiveRealRoots](OdlyzkoPoonen/Polynomial/PositiveRealRoots.lean)

Proved declarations: `HasBinaryEndpoints.eval_real_ge_one`, `HasBinaryEndpoints.eval_real_pos`, `monic_exists_positive_root_of_constant_neg`.

### [OdlyzkoPoonen.Polynomial.RationalReducibility](OdlyzkoPoonen/Polynomial/RationalReducibility.lean)

Definitions: `ReducibleOverRat`.

Proved declarations: `monic_reducibleOverRat_iff`, `monic_factors_of_reducibleOverRat`, `HasBinaryEndpoints.monic_factors_of_reducible`.

### [OdlyzkoPoonen.Polynomial.RationalSeparable](OdlyzkoPoonen/Polynomial/RationalSeparable.lean)

Proved declarations: `complex_roots_nodup_of_rational_irreducible`.

### [OdlyzkoPoonen.Polynomial.ReciprocalDivisorCandidates](OdlyzkoPoonen/Polynomial/ReciprocalDivisorCandidates.lean)

Proved declarations: `HasBinaryEndpoints.reciprocal_divisor_candidate_alternative`.

### [OdlyzkoPoonen.Polynomial.ReciprocalDivisorReduction](OdlyzkoPoonen/Polynomial/ReciprocalDivisorReduction.lean)

Proved declarations: `HasBinaryEndpoints.monic_divisor_constant`, `HasBinaryEndpoints.monic_divisor_reduce_endpoints`, `monic_reciprocal_reduce_dvd_gcd`, `HasBinaryEndpoints.reciprocal_divisor_degree_le_gcd`, `monic_reciprocal_divisor_reduction`.

### [OdlyzkoPoonen.Polynomial.Reduction](OdlyzkoPoonen/Polynomial/Reduction.lean)

Definitions: `reducePolynomial`, `zeroOneLift`, `CongruentMod`.

Proved declarations: `coeff_reducePolynomial`, `reducePolynomial_mul`, `coeff_zeroOneLift`, `zeroOneLift_binary`, `reduce_zeroOneLift`, `zeroOneLift_reduce`, `zeroOneLift_injective`, `IsBinary.eq_of_reduce_eq`, `support_zeroOneLift`, `natDegree_zeroOneLift`, `zeroOneLift_reverse`, `IsBinary.natDegree_reduce`, `IsBinary.reduce_reverse`, `congruentMod_iff_coeff_dvd`.

### [OdlyzkoPoonen.Polynomial.ResiduePolynomial](OdlyzkoPoonen/Polynomial/ResiduePolynomial.lean)

Definitions: `wordResiduePolynomial`, `residueEndpointShift`.

Proved declarations: `X_pow_sub_one_dvd_pow_sub_residue`, `wordPolynomial_sub_residue_dvd`, `cyclotomic_dvd_wordResiduePolynomial_iff`, `coeff_wordResiduePolynomial`, `coeff_wordResiduePolynomial_above`.

### [OdlyzkoPoonen.Polynomial.ResultantDivisibility](OdlyzkoPoonen/Polynomial/ResultantDivisibility.lean)

Proved declarations: `resultant_map_injective`, `monic_resultant_right_degree`, `pow_dvd_resultant_of_C_dvd_sub_mul`, `prime_pow_degree_dvd_resultant_comp_X_pow`.

### [OdlyzkoPoonen.Polynomial.Reversal](OdlyzkoPoonen/Polynomial/Reversal.lean)

Definitions: `autocorrelation`.

Proved declarations: `reverse_natDegree_of_constant_ne_zero`, `reverse_reverse_of_constant_ne_zero`, `IsBinary.reverse`, `HasBinaryEndpoints.reverse`, `HasBinaryEndpoints.reverse_reverse`, `autocorrelation_reverse`, `autocorrelation_mul`, `autocorrelation_factor_reverse`.

### [OdlyzkoPoonen.Polynomial.RootBound](OdlyzkoPoonen/Polynomial/RootBound.lean)

Proved declarations: `sum_range_pow_lt_pow_of_two_le`, `monic_root_norm_lt_two`, `HasBinaryEndpoints.root_norm_lt_two`, `HasBinaryEndpoints.divisor_root_norm_lt_two`.

### [OdlyzkoPoonen.Polynomial.RootFamilies](OdlyzkoPoonen/Polynomial/RootFamilies.lean)

Proved declarations: `exists_injective_complex_root_family`.

### [OdlyzkoPoonen.Polynomial.RootPowerBadPrimes](OdlyzkoPoonen/Polynomial/RootPowerBadPrimes.lean)

Definitions: `RootPowerSeparates`.

Proved declarations: `prod_bad_root_power_primes_le`, `root_power_injOn_transfer`, `prod_bad_complex_root_power_primes_le`, `prod_bad_integer_root_power_primes_le`.

### [OdlyzkoPoonen.Polynomial.RootPowerFamilies](OdlyzkoPoonen/Polynomial/RootPowerFamilies.lean)

Proved declarations: `polynomialRootPowers_prod_X_sub_C`, `exists_integer_root_family`, `root_power_family_factorization`, `root_power_family_injective`, `root_power_families_disjoint`.

### [OdlyzkoPoonen.Polynomial.RootPowerFamilyInjectivity](OdlyzkoPoonen/Polynomial/RootPowerFamilyInjectivity.lean)

Proved declarations: `option_prime_exponents_injective`, `root_power_pair_injective`.

### [OdlyzkoPoonen.Polynomial.RootPowerPrime](OdlyzkoPoonen/Polynomial/RootPowerPrime.lean)

Proved declarations: `exists_prime_separating_root_powers_of_product_lt`, `exists_prime_in_interval_separating_root_powers`, `exists_prime_separating_root_powers_of_log_lt`.

### [OdlyzkoPoonen.Polynomial.RootPowerResultants](OdlyzkoPoonen/Polynomial/RootPowerResultants.lean)

Proved declarations: `polynomialRootPowers_complex_monic`, `polynomialRootPowers_one_complex`, `polynomialRootPowers_int_monic`, `polynomialRootPowers_int_natDegree`, `resultant_rootPowers_eq_comp_complex`, `resultant_rootPowers_eq_comp_int`, `prime_pow_degree_dvd_rootPower_resultant`.

### [OdlyzkoPoonen.Polynomial.RootPowerRoots](OdlyzkoPoonen/Polynomial/RootPowerRoots.lean)

Proved declarations: `polynomialRootPowers_complex_ne_zero`, `polynomialRootPowers_complex_roots`, `rootPowers_isCoprime_of_distinct_exponents`.

### [OdlyzkoPoonen.Polynomial.RootProductResultants](OdlyzkoPoonen/Polynomial/RootProductResultants.lean)

Proved declarations: `resultant_prod_X_sub_C`, `norm_resultant_eq_root_product`, `eval_derivative_prod_X_sub_C`, `norm_resultant_derivative_eq_root_product`.

### [OdlyzkoPoonen.Polynomial.RootRatioOrders](OdlyzkoPoonen/Polynomial/RootRatioOrders.lean)

Definitions: `HasRootRatioOrder`.

Proved declarations: `hasRootRatioOrder_one`, `HasRootRatioOrder.mul_of_coprime`, `hasRootRatioOrder_prod_primes`, `prime_bad_power_hasRootRatioOrder`.

### [OdlyzkoPoonen.Polynomial.RootRatios](OdlyzkoPoonen/Polynomial/RootRatios.lean)

Definitions: `polynomialRootRatios`.

Proved declarations: `mem_polynomialRootRatios`, `card_polynomialRootRatios_le`, `algEquiv_map_mem_polynomialRootRatios`, `primitiveRoots_subset_polynomialRootRatios`, `totient_le_degree_sq_of_primitive_root_ratio`, `order_le_two_degree_four_of_primitive_root_ratio`.

### [OdlyzkoPoonen.Polynomial.SparseDivisorUniqueness](OdlyzkoPoonen/Polynomial/SparseDivisorUniqueness.lean)

Proved declarations: `word_eq_of_sparse_divisibility`.

### [OdlyzkoPoonen.Polynomial.SparseWords](OdlyzkoPoonen/Polynomial/SparseWords.lean)

Proved declarations: `expand_contract_of_coeff_eq_zero`, `coeff_wordPolynomial_sub_eq_zero_of_not_dvd`, `sparse_word_difference_expand`, `sparse_word_difference_contract_ne_zero`.

### [OdlyzkoPoonen.Polynomial.TaylorRootProducts](OdlyzkoPoonen/Polynomial/TaylorRootProducts.lean)

Proved declarations: `taylor_X_sub_C_self`, `taylor_coeff_pow_X_sub_C_mul`, `hasseDeriv_eval_pow_X_sub_C_mul`, `hasseDeriv_eval_pow_X_sub_C_mul_of_lt`, `prod_X_sub_C_factor_at`, `hasseDeriv_prod_X_sub_C_eval_multiplicity`, `hasseDeriv_prod_X_sub_C_eval_eq_zero_of_lt`.

### [OdlyzkoPoonen.Probability.AsymmetryGeometricSum](OdlyzkoPoonen/Probability/AsymmetryGeometricSum.lean)

Proved declarations: `asymmetry_weight_factor`, `sum_two_thirds_positive`, `sum_two_thirds_positive_le_two`, `asymmetry_geometric_sum_le`.

### [OdlyzkoPoonen.Probability.AsymmetryLaw](OdlyzkoPoonen/Probability/AsymmetryLaw.lean)

Proved declarations: `f2Probability_firstAsymmetryAt`, `HasF2Endpoints.exists_firstAsymmetry_range`, `f2Probability_firstAsymmetryAt_of_range`, `HasF2Endpoints.reverse_eq_of_degree_le_two`.

### [OdlyzkoPoonen.Probability.AverageBounds](OdlyzkoPoonen/Probability/AverageBounds.lean)

Proved declarations: `uniformAverage_const`, `uniformAverage_le`.

### [OdlyzkoPoonen.Probability.BernoulliCount](OdlyzkoPoonen/Probability/BernoulliCount.lean)

Definitions: `booleanWordFinsetEquiv`.

Proved declarations: `trueBitCount_eq_card`, `uniformProbability_trueBitCount`, `uniformProbability_trueBitCount_eq_zero`.

### [OdlyzkoPoonen.Probability.BinaryModel](OdlyzkoPoonen/Probability/BinaryModel.lean)

Definitions: `binaryProbability`.

Proved declarations: `binaryProbability_eq_count`, `binaryProbability_endpoints`.

### [OdlyzkoPoonen.Probability.BinomialAtoms](OdlyzkoPoonen/Probability/BinomialAtoms.lean)

Proved declarations: `uniformProbability_trueBitCount_le_central`, `uniformProbability_trueBitCount_le_sqrt`, `uniformProbability_bitValue_sum_le`, `uniformProbability_shifted_bitValue_sum_le`.

### [OdlyzkoPoonen.Probability.BitWeights](OdlyzkoPoonen/Probability/BitWeights.lean)

Definitions: `trueBitCount`.

Proved declarations: `pow_trueBitCount_eq_prod`, `sum_pow_trueBitCount`, `uniformAverage_pow_trueBitCount`, `uniformAverage_half_pow_trueBitCount`, `uniformAverage_triangular_half_weight`.

### [OdlyzkoPoonen.Probability.CyclotomicDegreeTwo](OdlyzkoPoonen/Probability/CyclotomicDegreeTwo.lean)

Proved declarations: `binaryProbability_cyclotomic_degree_two_fixed_le`, `binaryProbability_cyclotomic_degree_two_le`.

### [OdlyzkoPoonen.Probability.CyclotomicHighDegree](OdlyzkoPoonen/Probability/CyclotomicHighDegree.lean)

Proved declarations: `HasBinaryEndpoints.cyclotomic_order_le`, `binaryProbability_cyclotomic_divisible_le`, `binaryProbability_high_cyclotomic_le`.

### [OdlyzkoPoonen.Probability.CyclotomicIntermediateDegree](OdlyzkoPoonen/Probability/CyclotomicIntermediateDegree.lean)

Proved declarations: `binaryProbability_cyclotomic_intermediate_fixed_le`, `binaryProbability_cyclotomic_intermediate_le`.

### [OdlyzkoPoonen.Probability.CyclotomicRangeSum](OdlyzkoPoonen/Probability/CyclotomicRangeSum.lean)

Proved declarations: `binaryProbability_higher_cyclotomic_range_sum`.

### [OdlyzkoPoonen.Probability.CyclotomicResidueBound](OdlyzkoPoonen/Probability/CyclotomicResidueBound.lean)

Proved declarations: `binaryProbability_cyclotomic_residue_bound`, `binaryProbability_cyclotomic_residue_bound_degree`.

### [OdlyzkoPoonen.Probability.EventComplement](OdlyzkoPoonen/Probability/EventComplement.lean)

Proved declarations: `uniformProbability_not`, `binaryProbability_irreducible_eq_one_sub_reducible`.

### [OdlyzkoPoonen.Probability.FiniteBitSums](OdlyzkoPoonen/Probability/FiniteBitSums.lean)

Proved declarations: `uniformProbability_finite_bit_sum_le`.

### [OdlyzkoPoonen.Probability.FiniteBounds](OdlyzkoPoonen/Probability/FiniteBounds.lean)

Proved declarations: `uniformAverage_sum`, `uniformAverage_mul_right`, `uniformProbability_exists_le_sum`, `uniformProbability_product_bound`.

### [OdlyzkoPoonen.Probability.FiniteEvents](OdlyzkoPoonen/Probability/FiniteEvents.lean)

Proved declarations: `uniformAverage_add`, `uniformAverage_sub`, `uniformProbability_or_le_add`, `uniformProbability_sub_of_imp`, `binaryProbability_or_le_add`.

### [OdlyzkoPoonen.Probability.FiniteFieldModel](OdlyzkoPoonen/Probability/FiniteFieldModel.lean)

Definitions: `f2Probability`, `f2PairProbability`.

Proved declarations: `f2Probability_eq_count`, `f2Probability_eq_binaryProbability`, `f2Probability_endpoints`, `f2PairProbability_product`.

### [OdlyzkoPoonen.Probability.FiniteProduct](OdlyzkoPoonen/Probability/FiniteProduct.lean)

Proved declarations: `uniformProbability_pi`, `uniformProbability_pi_eq_le`, `uniformProbability_fiber_unique_le`.

### [OdlyzkoPoonen.Probability.FiniteSetUnion](OdlyzkoPoonen/Probability/FiniteSetUnion.lean)

Proved declarations: `uniformAverage_finset_sum`, `uniformProbability_exists_mem_le_sum`, `uniformProbability_exists_mem_le_card_mul`.

### [OdlyzkoPoonen.Probability.FiniteUniform](OdlyzkoPoonen/Probability/FiniteUniform.lean)

Definitions: `uniformProbability`.

Proved declarations: `uniformProbability_false`, `uniformProbability_true`, `uniformProbability_nonneg`, `uniformProbability_mono`, `uniformProbability_le_one`, `uniformProbability_product`.

### [OdlyzkoPoonen.Probability.FirstTrueBit](OdlyzkoPoonen/Probability/FirstTrueBit.lean)

Definitions: `FirstTrueAt`.

Proved declarations: `firstTrueAt_iff_prescribed`, `uniformProbability_firstTrueAt`, `FirstTrueAt.unique`, `exists_firstTrueAt_iff`.

### [OdlyzkoPoonen.Probability.FreshBitConstraints](OdlyzkoPoonen/Probability/FreshBitConstraints.lean)

Definitions: `DependsOnPrefix`, `TogglesOn`, `freshBitCorrection`.

Proved declarations: `freshBitCorrection_dependsOnEarlier`, `triangular_freshBitCorrection_active`, `triangular_freshBitCorrection_inactive`, `uniformProbability_freshBitConstraints`, `uniformProbability_all_outputs_zero_le`.

### [OdlyzkoPoonen.Probability.ImageBound](OdlyzkoPoonen/Probability/ImageBound.lean)

Proved declarations: `uniformProbability_exists_image_le`.

### [OdlyzkoPoonen.Probability.IntegerDivisibility](OdlyzkoPoonen/Probability/IntegerDivisibility.lean)

Proved declarations: `binaryProbability_divisible_eq_zero_of_constant`, `binaryProbability_divisible_eq_zero_of_degree`, `binaryProbability_monic_divisible_le`.

### [OdlyzkoPoonen.Probability.LeadingFalseBits](OdlyzkoPoonen/Probability/LeadingFalseBits.lean)

Definitions: `shiftedWordIndex`.

Proved declarations: `shiftedWordIndex_injective`, `trueBitCount_eq_shifted`.

### [OdlyzkoPoonen.Probability.MinusOne](OdlyzkoPoonen/Probability/MinusOne.lean)

Proved declarations: `uniformProbability_alternatingComplement`, `eval_wordPolynomial_minus_one_odd`, `eval_wordPolynomial_minus_one_even`, `binaryProbability_minus_one_odd`, `binaryProbability_minus_one_even`, `binaryProbability_minus_one_degree_one`, `binaryProbability_minus_one_degree_two`.

### [OdlyzkoPoonen.Probability.NoncyclotomicFactor](OdlyzkoPoonen/Probability/NoncyclotomicFactor.lean)

Proved declarations: `exists_uniform_noncyclotomic_factor_bound`, `exists_uniform_integer_irreducible_noncyclotomic_factor_bound`.

### [OdlyzkoPoonen.Probability.NoncyclotomicMonicFactor](OdlyzkoPoonen/Probability/NoncyclotomicMonicFactor.lean)

Proved declarations: `exists_uniform_noncyclotomic_monic_factor_bound`.

### [OdlyzkoPoonen.Probability.OppositeIndices](OdlyzkoPoonen/Probability/OppositeIndices.lean)

Definitions: `lowerWordIndex`, `upperWordIndex`, `centerWordIndex`.

Proved declarations: `lowerWordIndex_val`, `upperWordIndex_val`, `lowerWordIndex_lt_half`, `half_le_upperWordIndex`, `upperWordIndex_rev`, `centerWordIndex_val`, `centerWordIndex_rev`, `center_index_of_not_outer`.

### [OdlyzkoPoonen.Probability.OppositeWords](OdlyzkoPoonen/Probability/OppositeWords.lean)

Definitions: `assembleOppositeWord`, `oppositeWordEquiv`.

Proved declarations: `assembleOppositeWord_lower`, `assembleOppositeWord_upper`, `assembleOppositeWord_center`, `assembleOppositeWord_recover`, `uniformProbability_oppositeWord`.

### [OdlyzkoPoonen.Probability.PrescribedBits](OdlyzkoPoonen/Probability/PrescribedBits.lean)

Definitions: `prescribedBitsEquiv`.

Proved declarations: `card_prescribedBits`, `uniformProbability_prescribedBits`.

### [OdlyzkoPoonen.Probability.ReciprocalDivisorNormalization](OdlyzkoPoonen/Probability/ReciprocalDivisorNormalization.lean)

Proved declarations: `hasLargeReciprocalIntegerDivisor_iff`, `binaryProbability_reciprocal_noncyclotomic_unrestricted`.

### [OdlyzkoPoonen.Probability.ReciprocalIntegerDivisors](OdlyzkoPoonen/Probability/ReciprocalIntegerDivisors.lean)

Definitions: `HasLargeReciprocalIntegerDivisor`.

Proved declarations: `HasBinaryEndpoints.gcd_degree_of_large_reciprocal_divisor`, `binaryProbability_large_reciprocal_divisor_le`.

### [OdlyzkoPoonen.Probability.ReciprocalLaw](OdlyzkoPoonen/Probability/ReciprocalLaw.lean)

Proved declarations: `f2Probability_reciprocal`, `card_reciprocal_f2Family`.

### [OdlyzkoPoonen.Probability.ReciprocalNoncyclotomicFiniteBound](OdlyzkoPoonen/Probability/ReciprocalNoncyclotomicFiniteBound.lean)

Proved declarations: `exists_noncyclotomic_reciprocal_finite_bound`.

### [OdlyzkoPoonen.Probability.ReciprocalTail](OdlyzkoPoonen/Probability/ReciprocalTail.lean)

Definitions: `reciprocalGeometricTail`.

Proved declarations: `reciprocal_counting_summand`, `reciprocalGeometricTail_nonneg`, `reciprocalGeometricTail_succ`, `sum_reciprocal_tail_range`, `sum_reciprocal_counting_le_tail`, `two_rpow_neg_half_even`, `two_rpow_neg_half_odd`, `reciprocalGeometricTail_even`, `reciprocalGeometricTail_odd`, `reciprocalGeometricTail_le_rpow`, `sum_reciprocal_counting_le_rpow`.

### [OdlyzkoPoonen.Probability.ResidueBlocks](OdlyzkoPoonen/Probability/ResidueBlocks.lean)

Definitions: `residueIndex`, `residueFiberEquiv`, `residueBlockCoefficient`.

Proved declarations: `coeff_wordResiduePolynomial_eq_block`, `coeff_wordResiduePolynomial_grouped`, `card_residueIndex_fiber_add_one_ge`, `uniformProbability_residueBlockCoefficient_le`, `cyclotomic_dvd_determines_low_residue_coefficients`.

### [OdlyzkoPoonen.Probability.SelectedCoordinates](OdlyzkoPoonen/Probability/SelectedCoordinates.lean)

Proved declarations: `uniformProbability_selected_coordinates_le`.

### [OdlyzkoPoonen.Probability.SparseDivisorBound](OdlyzkoPoonen/Probability/SparseDivisorBound.lean)

Proved declarations: `uniformProbability_bool_eq`, `binaryProbability_divisible_le_sparse`, `binaryProbability_rational_irreducible_divisible_le_sparse`.

### [OdlyzkoPoonen.Probability.TriangularBits](OdlyzkoPoonen/Probability/TriangularBits.lean)

Definitions: `DependsOnEarlier`, `triangularBitMap`.

Proved declarations: `triangularBitMap_injective`, `triangularBitMap_bijective`, `uniformProbability_triangularBitMap`, `uniformProbability_triangular_prescribedBits`.

### [OdlyzkoPoonen.Probability.UniformAverage](OdlyzkoPoonen/Probability/UniformAverage.lean)

Definitions: `uniformAverage`.

Proved declarations: `uniformAverage_mono`, `uniformAverage_equiv`, `uniformAverage_bijective`, `uniformAverage_product`, `uniformProbability_eq_average_indicator`, `uniformProbability_product_eq_average`.

### [OdlyzkoPoonen.Probability.UniformTransport](OdlyzkoPoonen/Probability/UniformTransport.lean)

Proved declarations: `uniformProbability_equiv`, `uniformProbability_bijective`.

### [OdlyzkoPoonen.Probability.WordGrouping](OdlyzkoPoonen/Probability/WordGrouping.lean)

Definitions: `groupWordEquiv`.

Proved declarations: `groupWordEquiv_apply`, `uniformProbability_groupWord`, `uniformProbability_groupWord_pi`.

### [OdlyzkoPoonen.Probability.WordPrefix](OdlyzkoPoonen/Probability/WordPrefix.lean)

Definitions: `wordPrefix`, `prefixWordEquiv`.

Proved declarations: `uniformAverage_wordPrefix`.

### [OdlyzkoPoonen.Reducibility.EventBounds](OdlyzkoPoonen/Reducibility/EventBounds.lean)

Proved declarations: `reducible_without_cyclotomic_probability_le`, `reducible_sub_minus_one_probability_eq`, `reducible_sub_minus_one_probability_nonneg`, `reducible_sub_minus_one_probability_le`, `reducible_probability_reduction`.

### [OdlyzkoPoonen.Reducibility.FactorAlternative](OdlyzkoPoonen/Reducibility/FactorAlternative.lean)

Proved declarations: `HasBinaryEndpoints.companion_or_reciprocal_of_reducible`.

