# Odlyzko–Poonen

A Lean formalization of irreducibility and sharp reducibility estimates for
uniformly random monic binary integer polynomials with constant coefficient one.
The proof library now proves both main theorems, both numbered lemmas, the
factor-pair proposition, and all displayed estimates used in their proofs.

Submission preparation is in progress. The difference-multiset counting results,
their exponential error bounds, and arbitrary-order periodic half-power
expansions now have checked proofs. The explicit coefficients through degree
minus three halves and final submission verification remain unfinished. The historical build, Comparator,
kernel-replay and standalone-checkout records certify their recorded snapshots;
they do not certify the current development tree.
The repository has not been published or registered.

Formalization author and responsible maintainer: Constantin Kogler. Original
code and documentation use [0BSD](LICENSE). The mathematical work,
*The Odlyzko–Poonen conjecture*, is by Constantin Kogler; its contribution
statement credits GPT-6 Astra with the original proof and Kogler with rewriting
and checking the mathematical proof. Lean development uses AI assistance;
no independent human review of the formalization is claimed. Contained proof reuse is recorded in
[provenance/reused-source.json](provenance/reused-source.json).

## The mathematical statements

For each natural degree `n >= 1`, choose uniformly from the integer polynomials

    1 + p₁ X + ... + pₙ₋₁ Xⁿ⁻¹ + Xⁿ,  with each pᵢ in {0,1}.

There are exactly `2^(n-1)` such polynomials. Irreducibility is the standard
predicate after mapping coefficients to the rationals. The main theorem proves
that the probability of irreducibility tends to one. More precisely,

    Pr(reducible) = Pr(P(-1)=0) + O(1/n)
                 = sqrt(2/(pi*n)) + O(1/n).

The first probability difference is nonnegative for every `n >= 2`, and one
positive constant bounds it by `C/n` beyond one natural threshold.

The second main theorem bounds the probability of a binary polynomial `Q` of
the same degree, distinct from `P` and its reciprocal, having the same
coefficientwise autocorrelation modulo four:

    Pr(exists such Q) <= sum over d=1,...,floor(n/2) of
                          (3/4)^floor((n-d-1)/2)
                     <= 8*(3/4)^floor((n-1)/4).

The library uses the actual reciprocal polynomial, polynomial divisibility,
cyclotomic polynomials, finite uniform law and standard real Big-O/limit notions.
`binaryProbability m` counts `m` internal fair bits; the original degree `n`
therefore corresponds to `m=n-1`. `binaryProbability_eq_count` and
`mem_binaryFamily_iff` prove equivalence with the stated finite polynomial family.

[Literature and scope](reference/LiteratureAndScope.md) compares the exact
probability model with the historical conjecture and identifies the role of
the primary references. No independent novelty assessment is claimed.

## Results and source correspondence

All declarations below are in namespace `OdlyzkoPoonen`.

| Result | Principal declaration | Module |
| --- | --- | --- |
| Theorem 1.1, irreducibility limit | `odlyzko_poonen_irreducibility` | `Asymptotics/Reducibility` |
| Theorem 1.1, excess over minus-one event | `binaryProbability_reducible_excess_isBigO` | `Asymptotics/Reducibility` |
| Nonnegative excess with a uniform coefficient | `exists_reducible_probability_excess_bound` | `Asymptotics/Reducibility` |
| Theorem 1.1, sharp leading term | `binaryProbability_reducible_asymptotic` | `Asymptotics/Reducibility` |
| Theorem 1.2, both exact inequalities | `mod_four_companion_probability` | `ModFour/CompanionProbability` |
| Proposition 2.1, independent factor-pair probability | `factor_pair_congruence_probability` | `ModFour/FactorProbability` |
| (2.1), fresh-bit toggle | `autocorrelationDiscrepancy_togglePair` | `ModFour/ExposureToggle` |
| (2.2), conditional fiber bound | `paired_discrepancies_zero_fiber_probability_le` | `ModFour/FiberEstimate` |
| Lemma 3.1, full monic factor reversal | `binary_factor_reversal` | `Polynomial/FactorReversal` |
| (3.1), reciprocal gcd tail | `reciprocal_gcd_probability_le_eight` | `Asymptotics/ReciprocalBounds` |
| (3.2), uniform noncyclotomic factor bound | `exists_uniform_noncyclotomic_factor_bound` | `Probability/NoncyclotomicFactor` |
| (3.2), integer-ring irreducibility version | `exists_uniform_integer_irreducible_noncyclotomic_factor_bound` | `Probability/NoncyclotomicFactor` |
| Lemma 3.2, exact finite two-term estimate | `exists_unrestricted_reciprocal_finite_bound_eight` | `Asymptotics/ReciprocalBounds` |
| Lemma 3.2, every real decay exponent | `binaryProbability_unrestricted_reciprocal_noncyclotomic_isBigO` | `Asymptotics/ReciprocalDivisorNormalization` |
| (3.3), reducibility without cyclotomic factors | `binaryProbability_reducible_noncyclotomic_isBigO` | `Asymptotics/ReducibleNoncyclotomic` |
| (3.4), full higher-cyclotomic estimate | `binaryProbability_higher_cyclotomic_isBigO` | `Asymptotics/HigherCyclotomic` |
| Exact odd/even binomial formulas | `binaryProbability_minus_one_odd`, `binaryProbability_minus_one_even` | `Probability/MinusOne` |
| Stronger minus-one remainder | `binaryProbability_minus_one_asymptotic` | `Asymptotics/MinusOneAsymptotic` |
| Signed difference-multiset count and exponential error | `differenceMultisetFamily_card_bounds`, `differenceMultisetFamily_asymptotic` | `Combinatorics/DifferenceMultisetCount`, `Asymptotics/DifferenceMultisets` |
| Free upper endpoint with the same exponential rate | `anchoredDifferenceMultisetFamily_exponential_asymptotic` | `Asymptotics/AnchoredDifferenceRate` |
| Finite cyclotomic approximation to every inverse power | `binaryProbability_reducible_finite_cyclotomic_approximation` | `Asymptotics/FiniteCyclotomicApproximation` |
| Parity-dependent minus-one correction | `binaryProbability_minus_one_first_correction_asymptotic` | `Asymptotics/MinusOneExpansion` |

The fixed-factor estimate has one positive real constant and one sufficiently
large degree threshold, both independent of the factor. Its exponential rate is
`exp(-a*n/(log n)^4)`, with real division and logarithms. Monicity, constant-term,
degree, root-separation and quantitative Mahler assumptions are all discharged.
The final versions include sign, nonmonic and impossible-divisibility cases.

Lemma 3.2 retains the exact finite bound
`exp(4*L^2-a*n/(log n)^4) + 6*2^(-L/2)` for every natural cutoff `L` and all
sufficiently large `n`. Its normalized internal event is a nonconstant monic reciprocal divisor
*together with absence of a cyclotomic divisor of the original polynomial*.
The cutoff proof permits every real `A>0` in `O_A(n^(-A))`.
`hasLargeReciprocalIntegerDivisor_iff` proves equivalence with unrestricted
reciprocal integer divisors of a monic polynomial. The two independently
compared Lemma 3.2 estimates use unrestricted witnesses explicitly.

The arithmetic input is proved internally. In particular,
`exists_uniform_quantitative_log_mahler_bound` gives one absolute `c>0` and
threshold with `c/(log n)^3 <= log M(J)` for all relevant irreducible factors of
degree at most `n`. The large-degree coefficient is `1/18576`; a fixed gap
handles the finite exceptional degrees. A proved coarse determinant bound and
controlled separating primes suffice. No Breuillard–Varju estimate or Riemann
hypothesis is assumed. The higher-cyclotomic bound has absolute eventual
coefficient `2052`, and the minus-one remainder has coefficient `18` at rate
`n^(-3/2)` for every `n>=3`.

## Library layout and reading order

The public root [OdlyzkoPoonen.lean](OdlyzkoPoonen.lean) imports every proved
module. Supporting lemmas are separated by mathematical purpose:

- `Polynomial/`: binary coefficients, ordinary reversal, factorization,
  cyclotomic predicates, root bounds, sparse differences and normalization.
- `FiniteField/`: endpoint-one families over the field of two elements,
  reduction/lifting, gcd parametrization and reciprocal counts.
- `Probability/`: finite uniform counting, transport, conditioning, independence,
  event bounds, binomial masses and fixed-factor/cyclotomic probabilities.
- `ModFour/`: autocorrelation discrepancy, opposite-pair exposure, fresh-bit
  toggles, triangular laws and the two main companion/factor-pair bounds.
- `Arithmetic/`: totient and prime estimates, root-ratio orders, prime-family
  selection, residue counts and exact sparse quotient bounds.
- `LinearAlgebra/`: Hasse/confluent Vandermonde matrices, repeated-node counts,
  determinant identities and upper/lower bounds.
- `Analysis/`: Mahler measure, quantitative determinant parameters, logarithmic
  scales, real-power estimates and cutoff arguments.
- `Reducibility/`: canonical rational reducibility, factor alternatives and
  finite event reductions.
- `Asymptotics/`: the cyclotomic and noncyclotomic rates, parity combination,
  sharp reducibility asymptotics and irreducibility limit.

A useful dependency order is:

1. Read `Polynomial/Binary`, `BinaryWords`, `Reversal`, `Autocorrelation` and
   `Probability/FiniteUniform`, `BinaryModel` for the exact models.
2. Follow `FiniteField/BinaryFamily` through the opposite-pair and fresh-bit
   modules to `ModFour/FactorProbability` and `CompanionProbability`.
3. Read `Polynomial/FactorReversal`, the reciprocal gcd/count modules and
   `Reducibility/EventBounds` for the finite reduction of the main problem.
4. Follow root ratios and prime selection, confluent determinants and resultants,
   then `Analysis/UniformQuantitativeMahler` for the uniform arithmetic input.
5. Read `Probability/SparseDivisorBound`, `NoncyclotomicFactor` and
   `ReciprocalNoncyclotomicFiniteBound`, followed by the cutoff asymptotics.
6. Read the cyclotomic concentration/range modules and `Asymptotics/HigherCyclotomic`.
7. Read `Probability/MinusOne` and the parity/asymptotic modules, then
   `Asymptotics/Reducibility` for the final conclusions.

## Independent statement and submission files

[Challenge.lean](Challenge.lean) is a 356-line independent statement surface with
30 claims selected for comparison, explicit definitions and ordinary-language explanations.
It imports Mathlib only. [Solution.lean](Solution.lean) imports the proved library
and excludes the Challenge, whose deliberate theorem placeholders are confined
to that file. The default build checks both the library and Solution.

[COVERAGE.md](COVERAGE.md) indexes all 928 proof
declarations and 115 definitions or structures. [formalization.yaml](formalization.yaml) records
attribution, source relationships, AI assistance, review status and scope.
The mathematical work is attributed to Constantin Kogler. No public identifier,
independent novelty assessment, or separate human review is claimed.

Verification scripts and pinned CI live in `scripts/` and `.github/workflows/`.
Compact preservation records are in `verification/`; full generated logs are
ignored. The metadata schema is contained under `reference/palomar/schema/`
with its Apache-2.0 notice. Other original source and documentation use 0BSD.

## Checking the current library

The toolchain is pinned to Lean `4.34.0-rc2`; the committed manifest pins Mathlib
revision `85e3a25e006c35636f0e53b0e9296caca2685bc0` and its dependency closure.

```bash
lake build
lake env lean Verification.lean
```

[Verification.lean](Verification.lean) prints all 928 proved declarations,
115 definitions or structures, and the complete theorem axiom lists. The current
development check passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Metadata, license-file integrity, import isolation, and preservation of the
182 original proof modules passed structural validation. The final official
build, strict comparison, proof replays, license detection, and fresh-checkout
verification remain to be run for the completed submission. Records in
[verification/](verification/) document historical snapshots.

To reproduce the final checks after resolving the pinned dependencies:

```bash
python3 scripts/check_official.py local-build lake build
python3 scripts/check_official.py local-statements lake env lean Verification.lean
python3 scripts/audit_full_statements.py logs/verification/local-statements
python3 -m venv .lake/palomar-validation
.lake/palomar-validation/bin/python -m pip install -r scripts/requirements-palomar.txt
.lake/palomar-validation/bin/python scripts/validate_palomar.py
python3 scripts/check_official.py local-license python3 scripts/verify_license.py
python3 scripts/check_official.py local-comparator python3 scripts/verify_palomar.py
```

Use a fresh label for each run to preserve its evidence. Comparator preparation
requires Git, Go 1.24.0, Rust/Cargo 1.88.0 and the pinned Lean toolchain. License
detection uses Ruby 3.3.12 and the locked Gemfile (`bundle install` first).
The pinned CI describes the same prerequisites. No remote CI result or
registry acceptance is claimed.
