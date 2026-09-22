import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The Odlyzko–Poonen conjecture on irreducibility of random polynomials

For degree n>=1, choose uniformly among the 2^(n-1) monic integer
polynomials with constant coefficient one and intermediate coefficients in {0,1}.
We state three main theorems: the irreducibility limit and leading reducibility
asymptotic, the cyclotomic factorization bounds, and the modulo-four
reciprocal-product companion bound. Definitions and three preliminary lemmas
identify the finite uniform probability model used in these statements.

The argument m of binaryProbability counts internal bits: degree n uses m=n-1.
At degree zero this expression is a total extension; asymptotic statements
concern n tending to infinity, and finite bounds have explicit degree conditions.
Irreducibility is over the rationals in Theorem 1.1 and over the integers for
the remainder in Theorem 1.2. Cyclotomic products allow repeated factors and
the empty product. The same positive constants work in both bounds of Theorem 1.2.
Natural division in exponents means floor division, logarithms are natural,
and Big-O means one uniform constant beyond one threshold.

The definitions are explicit, and imports come from Mathlib. Deliberate theorem
holes specify the independent claims; Solution supplies the checked proofs
without importing this file.
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

/-- Failure of the standard irreducibility predicate after mapping to rational coefficients. -/
def ReducibleOverRat (p : ℤ[X]) : Prop :=
  ¬ Irreducible (p.map (Int.castRingHom ℚ))

/-- Divisibility by the ordinary cyclotomic polynomial of some positive order. -/
def HasCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 0 < k ∧ cyclotomic k ℤ ∣ p

/-- A finite product of positive-order cyclotomic polynomials, allowing multiplicity and the empty product. -/
def IsCyclotomicProduct (P : ℤ[X]) : Prop :=
  ∃ ks : List ℕ, (∀ k ∈ ks, 0 < k) ∧ P = (ks.map (fun k ↦ cyclotomic k ℤ)).prod

/-- A cyclotomic product times one irreducible integer polynomial with no cyclotomic divisor. -/
def HasIrreducibleNoncyclotomicPart (P : ℤ[X]) : Prop :=
  ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
    Irreducible R ∧ ¬ HasCyclotomicDivisor R

/-- The same factorization with a real upper bound on the cyclotomic degree. -/
def HasIrreducibleNoncyclotomicPartWithDegree (B : ℝ) (P : ℤ[X]) : Prop :=
  ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
    Irreducible R ∧ ¬ HasCyclotomicDivisor R ∧ (Q.natDegree : ℝ) ≤ B

/-- The ordinary polynomial product P times its degree-based reciprocal. -/
noncomputable def autocorrelation (p : ℤ[X]) : ℤ[X] := p * p.reverse

/-- Map every integer coefficient to its residue modulo r. -/
noncomputable def reducePolynomial (r : ℕ) (p : ℤ[X]) : (ZMod r)[X] :=
  p.map (Int.castRingHom (ZMod r))

/-- Polynomial congruence: equality after coefficientwise reduction modulo r. -/
def CongruentMod (r : ℕ) (p q : ℤ[X]) : Prop :=
  reducePolynomial r p = reducePolynomial r q

/-- A degree-n endpoint-one binary Q, distinct from P and its reciprocal, whose autocorrelation agrees modulo four. -/
def HasModFourCompanion (n : ℕ) (p : ℤ[X]) : Prop :=
  ∃ q : ℤ[X], HasBinaryEndpoints n q ∧ q ≠ p ∧ q ≠ p.reverse ∧
    CongruentMod 4 (autocorrelation p) (autocorrelation q)

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

/-- Theorem 1.1: rational irreducibility has probability tending to one, and the
reducibility probability is sqrt(2/(pi*n)) with error O(1/n). -/
theorem irreducibility_and_reducibility_asymptotic :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ)))) atTop (𝓝 1) ∧
    ((fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ))) := by
  sorry

/-- Theorem 1.2: with probability at least 1-C*exp(-c*n/(log n)^4), a cyclotomic
product times one irreducible noncyclotomic integer polynomial exists. With
probability at least 1-C*exp(-c*sqrt(n)), such a factorization has cyclotomic
degree at most sqrt(n). The same absolute positive constants work for n>=3. -/
theorem cyclotomic_irreducible_factorization_probability :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      (1 - C * Real.exp (-c * n / Real.log (n : ℝ) ^ 4) ≤
        binaryProbability (n - 1) HasIrreducibleNoncyclotomicPart) ∧
      (1 - C * Real.exp (-c * Real.sqrt (n : ℝ)) ≤
        binaryProbability (n - 1)
          (HasIrreducibleNoncyclotomicPartWithDegree (Real.sqrt (n : ℝ)))) := by
  sorry

/-- Theorem 1.3: the probability of a distinct degree-n binary polynomial, other
than the sampled polynomial or its reciprocal, with the same reciprocal product
modulo four is at most 8*(3/4)^floor((n-1)/4), for every n>=1. -/
theorem mod_four_companion_probability_le (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
      8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
  sorry

end OdlyzkoPoonen
