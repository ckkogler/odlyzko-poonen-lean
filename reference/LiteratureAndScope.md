# Literature, model and scope

## Which conjecture is stated?

The title refers to the irreducibility question for monic integer polynomials
of degree `n`, with constant coefficient one and each of the `n-1` internal
coefficients independently chosen from `{0,1}` with equal probability. This
is the model explicitly displayed in the introduction of
[Breuillard–Varjú, version 2, equation (1.1)](https://arxiv.org/html/1810.13360v2#S1),
where the conjecture is attributed to Odlyzko and Poonen. The historical
[Odlyzko–Poonen introduction](https://www.cecm.sfu.ca/organics/papers/odlyzko/paper/html/node1.html)
excludes zero constant coefficients and discusses the conjectured prevalence
of rational irreducibility. Their paper is *Zeros of polynomials with 0,1
coefficients*, L’Enseignement Mathématique (2) 39 (1993), 317–348.

The work being formalized, *The Odlyzko–Poonen conjecture*, is by Constantin
Kogler.

## Exact correspondence with the Lean model

| Mathematical object | Definition or checked correspondence |
| --- | --- |
| An internal word of `n-1` independent fair bits | `Fin (n-1) → Bool`, with `uniformProbability` |
| The polynomial `1 + p₁X + ... + pₙ₋₁Xⁿ⁻¹ + Xⁿ` | `wordPolynomial`; `m` internal bits give degree `m+1` |
| All eligible degree-`n` polynomials, each once | `binaryFamily`, `mem_binaryFamily_iff`, `wordPolynomial_injective` |
| Uniform counting, with denominator `2^(n-1)` | `card_binaryFamily`, `binaryProbability_eq_count` |
| Irreducibility over the rationals | `Irreducible (P.map (Int.castRingHom ℚ))` |
| Reducibility | `ReducibleOverRat`, the negation of that standard predicate |
| Degree tending to infinity | Mathlib `Filter.atTop` on the natural numbers |
| Probability of irreducibility tends to one | `odlyzko_poonen_irreducibility` |

All declaration names in this table have namespace `OdlyzkoPoonen`. The first
three claims in `Challenge.lean` expose the family and its probability law,
so the main statement cannot quietly change the sampling distribution. Both
endpoints are deterministically one. No factorization or reciprocal condition
is imposed on the sampled family. Degree zero is a total extension used only
to make the sequence a function on all natural numbers; the asymptotic
statements and finite bounds retain their stated degree ranges.

## Relationship to the cited results

Breuillard and Varjú's *Irreducibility of random polynomials of large degree*,
Acta Mathematica 223 (2019), 195–249, proves an irreducibility theorem under RH
for appropriate Dedekind zeta functions. Its introduction uses the same binary
model. This repository does not invoke that conditional theorem. The
fixed-factor and cyclotomic estimates needed here are separately proved in
Lean, using the uniform arithmetic, sparse-divisor and concentration machinery
indexed in `COVERAGE.md`. The metadata identifies the relevant local inputs,
rather than claiming a formalization of all their general results.
[Version 2 and publication information](https://arxiv.org/abs/1810.13360v2).

Bary-Soroker, Koukoulopoulos and Kozma's *Irreducibility of random polynomials:
general measures*, Inventiones Mathematicae 233 (2023), 1041–1120, provides a
useful comparison. Theorem 1 gives an eventual positive lower bound for uniform
coefficient sets of 2–34 consecutive integers, and convergence to one for at
least 35. Their general small-factor theorem excludes factors below a positive
fraction of the degree with high probability. The binary model corresponds
to the two-element set with the constant conditioned to be nonzero. The new
library's stated limit and sharp asymptotics are stronger conclusions for this
specific model; the broader coefficient and Galois-group results of that paper
are outside its scope.
[Version 3, Theorems 1–2](https://arxiv.org/html/2007.14567v3#S1).

The quantitative Mahler argument is documented separately from the sharper
external height bounds. Paul Voutier's *An effective lower bound for the height
of algebraic numbers* informs its determinant method, but the library proves a
coarser uniform logarithmic gap sufficient for the fixed-factor estimate.
It does not claim Voutier's full bound.
[Author's arXiv record](https://arxiv.org/abs/1211.3110).

These are comparisons with identified versions of relevant primary sources,
not an exhaustive novelty search or a claim about the current publication
status of the conjecture. No literature statement substitutes for a Lean proof.
The full source-to-declaration map is in `COVERAGE.md`; the metadata and
verification records state which machine checks have actually finished.
There is no independent human review or registry acceptance to report.
