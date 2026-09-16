import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The Odlyzko–Poonen conjecture: independent statements

For degree n>=1, choose uniformly among the 2^(n-1) monic integer
polynomials with constant one and all remaining coefficients in {0,1}.
Irreducibility is over the rationals. This file independently specifies both
main theorems, the factor-pair proposition, both numbered lemmas and the
principal estimates, together with the exact finite probability model.

The argument m of binaryProbability counts internal bits: degree n uses m=n-1.
At degree zero that expression is merely a total extension; all finite-degree
claims impose their stated lower bound, and limits concern n tending to infinity.
Natural division in exponents means floor division. Logarithms are natural,
and real powers have real exponents. Big-O is Mathlib's norm bound by one
constant beyond one threshold; these may depend on A in the two statements
with A>0. Constants in the fixed-factor estimate precede both n and the factor.

Only foundational Mathlib modules are imported. Deliberate theorem holes are
confined to this independent statement file. Solution imports the proved
library and never imports this file. Every definition below is explicit.
-/

noncomputable section
open Polynomial Filter Asymptotics
open scoped BigOperators Topology Classical
namespace OdlyzkoPoonen

/-- Every coefficient is zero or one. -/
def IsBinary (p : ℤ[X]) : Prop := ∀ k, p.coeff k = 0 ∨ p.coeff k = 1

/-- Monic degree-n integer polynomials with constant one and binary coefficients. -/
structure HasBinaryEndpoints (n : ℕ) (p : ℤ[X]) : Prop where
  monic : p.Monic
  degree : p.natDegree = n
  constant : p.coeff 0 = 1
  binary : IsBinary p

/-- Interpret a Boolean as the integer zero or one. -/
def bitValue (b : Bool) : ℤ := if b then 1 else 0

/-- Place the m internal bits in coefficients one through m. -/
noncomputable def interiorPolynomial {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  ∑ i : Fin m, C (bitValue (w i)) * X ^ (i.val + 1)

/-- Add the constant and leading coefficients, both one; the degree is m+1. -/
noncomputable def wordPolynomial {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  1 + interiorPolynomial w + X ^ (m + 1)

/-- The finite image of all internal words. -/
noncomputable def binaryFamily (m : ℕ) : Finset ℤ[X] :=
  Finset.univ.image (@wordPolynomial m)

/-- The number of outcomes satisfying E divided by the cardinality of the finite space. -/
noncomputable def uniformProbability {α : Type*} [Fintype α] (E : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / Fintype.card α

/-- Uniform independent internal bits, pushed forward to their integer polynomial. -/
noncomputable def binaryProbability (m : ℕ) (E : Polynomial ℤ → Prop) : ℝ :=
  uniformProbability (fun w : Fin m → Bool ↦ E (wordPolynomial w))

/-- The ordinary polynomial product P times its degree-based reciprocal. -/
noncomputable def autocorrelation (p : ℤ[X]) : ℤ[X] := p * p.reverse

/-- Map every integer coefficient to its residue modulo r. -/
noncomputable def reducePolynomial (r : ℕ) (p : ℤ[X]) : (ZMod r)[X] :=
  p.map (Int.castRingHom (ZMod r))

/-- Polynomial congruence: equality after coefficientwise reduction modulo r. -/
def CongruentMod (r : ℕ) (p q : ℤ[X]) : Prop :=
  reducePolynomial r p = reducePolynomial r q

/-- Lift every coefficient in F2 to its unique representative zero or one. -/
noncomputable def zeroOneLift (p : (ZMod 2)[X]) : ℤ[X] :=
  p.sum (fun k c ↦ monomial k (c.val : ℤ))

/-- Reduce an endpoint-one binary polynomial to F2. -/
noncomputable def f2WordPolynomial {m : ℕ} (w : Fin m → Bool) : (ZMod 2)[X] :=
  reducePolynomial 2 (wordPolynomial w)

/-- Uniform product counting on two independent internal-bit words over F2. -/
noncomputable def f2PairProbability (m l : ℕ)
    (E : Polynomial (ZMod 2) → Polynomial (ZMod 2) → Prop) : ℝ :=
  uniformProbability (fun w : (Fin m → Bool) × (Fin l → Bool) ↦
    E (f2WordPolynomial w.1) (f2WordPolynomial w.2))

/-- A degree-n endpoint-one binary Q, distinct from P and its reciprocal, whose autocorrelation agrees modulo four. -/
def HasModFourCompanion (n : ℕ) (p : ℤ[X]) : Prop :=
  ∃ q : ℤ[X], HasBinaryEndpoints n q ∧ q ≠ p ∧ q ≠ p.reverse ∧
    CongruentMod 4 (autocorrelation p) (autocorrelation q)

/-- Failure of the standard irreducibility predicate after mapping to rational coefficients. -/
def ReducibleOverRat (p : ℤ[X]) : Prop :=
  ¬ Irreducible (p.map (Int.castRingHom ℚ))

/-- Divisibility by the ordinary cyclotomic polynomial of some positive order. -/
def HasCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 0 < k ∧ cyclotomic k ℤ ∣ p

/-- A cyclotomic divisor of degree at least two; its degree equals the Euler totient. -/
def HasHigherCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 2 ≤ k.totient ∧ cyclotomic k ℤ ∣ p

/-- Model: the sampled family consists exactly of monic endpoint-one binary polynomials of degree m+1. -/
lemma mem_binaryFamily_iff {m : ℕ} {p : ℤ[X]} :
    p ∈ binaryFamily m ↔ HasBinaryEndpoints (m + 1) p := by
  sorry

/-- Model: precisely 2^m polynomials have m internal binary coefficients. -/
lemma card_binaryFamily (m : ℕ) : (binaryFamily m).card = 2 ^ m := by
  sorry

/-- Model: fair independent internal bits give uniform counting on the polynomial family. -/
lemma binaryProbability_eq_count (m : ℕ) (E : Polynomial ℤ → Prop) :
    binaryProbability m E = ((binaryFamily m).filter E).card / (2 : ℝ) ^ m := by
  sorry

/-- Theorem 1.1: the probability of irreducibility over the rationals tends to one. -/
theorem odlyzko_poonen_irreducibility :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ)))) atTop (𝓝 1) := by
  sorry

/-- Theorem 1.1: reducibility differs from the minus-one root event by O(1/n). -/
lemma binaryProbability_reducible_excess_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0)) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  sorry

/-- Theorem 1.1: one positive constant bounds that nonnegative difference by C/n for all sufficiently large degrees. -/
theorem exists_reducible_probability_excess_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      0 ≤ binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0) ∧
      binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0) ≤ C / (n : ℝ) := by
  sorry

/-- Theorem 1.1: the reducibility probability is sqrt(2/(pi*n)) with O(1/n) error. -/
theorem binaryProbability_reducible_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  sorry

/-- Theorem 1.2: the probability of a genuine modulo-four companion is bounded by the exact degree-split sum, itself at most 8*(3/4)^floor((n-1)/4). -/
theorem mod_four_companion_probability (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
        (∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) ∧
      (∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) ≤
        8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
  sorry

/-- Proposition 2.1: independent uniform degree-d and degree-e endpoint-one polynomials over F2 satisfy the joint nonreciprocity/congruence event with probability at most 2*(3/4)^floor((e-1)/2). -/
theorem factor_pair_congruence_probability (d e : ℕ) (hd : 1 ≤ d) (hde : d ≤ e) :
    f2PairProbability (d - 1) (e - 1) (fun a b ↦ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      2 * (3 / 4 : ℝ) ^ ((e - 1) / 2) := by
  sorry

/-- Lemma 3.1: reversing either monic integer factor preserves binarity and autocorrelation; the two trivial outcomes occur exactly when the corresponding factor is reciprocal. Both factors have constant one. -/
theorem binary_factor_reversal {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    a.coeff 0 = 1 ∧ b.coeff 0 = 1 ∧ HasBinaryEndpoints n (a * b.reverse) ∧
      autocorrelation (a * b.reverse) = autocorrelation p ∧
      (a * b.reverse = p ↔ b = b.reverse) ∧
      (a * b.reverse = p.reverse ↔ a = a.reverse) := by
  sorry

/-- Estimate (3.1): the degree of the gcd of the reduction modulo two and its reciprocal has tail at most 6*2^(-L/2). This includes every natural cutoff L. -/
theorem reciprocal_gcd_probability {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (fun p ↦
      L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  sorry

/-- Estimate (3.2): one absolute positive a and threshold work for every degree and every rationally irreducible noncyclotomic integer factor, with rate exp(-a*n/(log n)^4). No monicity assumption is needed. -/
lemma exists_uniform_noncyclotomic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], Irreducible (J.map (Int.castRingHom ℚ)) →
        (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  sorry

/-- Estimate (3.2), also with ordinary irreducibility in the integer polynomial ring, including all signs and constant cases. -/
lemma exists_uniform_integer_irreducible_noncyclotomic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], Irreducible J → (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  sorry

/-- Lemma 3.2, finite bound: a nonconstant reciprocal divisor with no cyclotomic divisor of the original polynomial has probability at most exp(4*L^2-a*n/(log n)^4)+6*2^(-L/2), uniformly in L. -/
lemma exists_unrestricted_reciprocal_finite_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      binaryProbability (n - 1) (fun P ↦
        (∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ 1 ≤ J.natDegree) ∧
          ¬ HasCyclotomicDivisor P) ≤
        Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
          6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  sorry

/-- Lemma 3.2: the same reciprocal/noncyclotomic event has probability O_A(n^(-A)) for every real A>0. -/
lemma binaryProbability_unrestricted_reciprocal_noncyclotomic_isBigO
    (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      (∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ 1 ≤ J.natDegree) ∧
        ¬ HasCyclotomicDivisor P)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  sorry

/-- Estimate (3.3): reducibility without any cyclotomic divisor has probability O_A(n^(-A)) for every real A>0. -/
lemma binaryProbability_reducible_noncyclotomic_isBigO (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  sorry

/-- Estimate (3.4): the probability of a cyclotomic factor of degree at least two is O(1/n). -/
theorem binaryProbability_higher_cyclotomic_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) HasHigherCyclotomicDivisor) =O[atTop]
      (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  sorry

/-- Exact odd-degree formula: for degree 2r+1 the minus-one root probability is choose(2r,r)/2^(2r), including degree one. -/
theorem binaryProbability_minus_one_odd (r : ℕ) :
    binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) =
      ((2 * r).choose r : ℝ) / (2 : ℝ) ^ (2 * r) := by
  sorry

/-- Exact even-degree formula: for degree 2r the probability is choose(2r-1,r+1)/2^(2r-1), including the zero value at degree two. -/
theorem binaryProbability_minus_one_even {r : ℕ} (hr : 1 ≤ r) :
    binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) =
      ((2 * r - 1).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r - 1) := by
  sorry

/-- Minus-one asymptotic: its probability is sqrt(2/(pi*n)) with the stronger O(n^(-3/2)) error. -/
theorem binaryProbability_minus_one_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  sorry

end OdlyzkoPoonen
