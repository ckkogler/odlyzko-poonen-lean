import OdlyzkoPoonen.Polynomial.BinaryWords
import Mathlib.Data.Finset.Powerset

/-!
# Endpoint-fixed subsets and their binary polynomials

Subsets of `{0, ..., n}` containing both endpoints correspond exactly to the
degree-`n` binary polynomial family. The correspondence uses the sum of the
monomials indexed by the set and has support as its inverse.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

noncomputable def setPolynomial (A : Finset ℕ) : ℤ[X] := ∑ a ∈ A, X ^ a

lemma coeff_setPolynomial (A : Finset ℕ) (k : ℕ) :
    (setPolynomial A).coeff k = if k ∈ A then 1 else 0 := by
  classical
  simp [setPolynomial, finsetSum_coeff, Polynomial.coeff_X_pow]

lemma support_setPolynomial (A : Finset ℕ) : (setPolynomial A).support = A := by
  classical
  ext k
  simp [mem_support_iff, coeff_setPolynomial]

lemma setPolynomial_injective : Function.Injective setPolynomial := by
  intro A B h
  simpa only [support_setPolynomial] using congrArg Polynomial.support h

lemma setPolynomial_binary (A : Finset ℕ) : IsBinary (setPolynomial A) := by
  classical
  intro k
  rw [coeff_setPolynomial]
  split_ifs <;> simp

/-- Subsets of the integer interval from zero to `n` containing both endpoints. -/
def binarySetFamily (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range (n + 1)).powerset).filter (fun A ↦ 0 ∈ A ∧ n ∈ A)

lemma mem_binarySetFamily_iff {n : ℕ} {A : Finset ℕ} :
    A ∈ binarySetFamily n ↔ (∀ a ∈ A, a ≤ n) ∧ 0 ∈ A ∧ n ∈ A := by
  simp only [binarySetFamily, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_range, Nat.lt_succ_iff]

lemma setPolynomial_endpoints {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) : HasBinaryEndpoints n (setPolynomial A) := by
  obtain ⟨hbound, hzero, htop⟩ := mem_binarySetFamily_iff.mp hA
  have hdeg : (setPolynomial A).natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      rw [coeff_setPolynomial, ite_eq_right (by
        intro hkA
        exact (not_le_of_gt hk) (hbound k hkA))]
    · simp [coeff_setPolynomial, htop]
  refine ⟨?_, hdeg, ?_, setPolynomial_binary A⟩
  · change (setPolynomial A).coeff (setPolynomial A).natDegree = 1
    simp [hdeg, coeff_setPolynomial, htop]
  · simp [coeff_setPolynomial, hzero]

lemma HasBinaryEndpoints.support_mem_binarySetFamily {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.support ∈ binarySetFamily n := by
  apply mem_binarySetFamily_iff.mpr
  refine ⟨fun a ha ↦ hp.degree ▸ le_natDegree_of_mem_supp a ha, ?_, ?_⟩
  · simp [mem_support_iff, hp.constant]
  · rw [mem_support_iff, hp.coeff_degree]
    exact one_ne_zero

lemma setPolynomial_support_of_binary {p : ℤ[X]} (hp : IsBinary p) :
    setPolynomial p.support = p := by
  classical
  ext k
  rw [coeff_setPolynomial]
  rcases hp k with hk | hk <;> simp [mem_support_iff, hk]

/-- The set model and the polynomial model have exactly the same elements. -/
theorem binarySetFamily_image_setPolynomial {n : ℕ} (hn : 1 ≤ n) :
    (binarySetFamily n).image setPolynomial = binaryFamily (n - 1) := by
  classical
  ext p
  rw [Finset.mem_image, mem_binaryFamily_iff, Nat.sub_add_cancel hn]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact setPolynomial_endpoints hA
  · intro hp
    exact ⟨p.support, hp.support_mem_binarySetFamily, setPolynomial_support_of_binary hp.binary⟩

theorem card_binarySetFamily {n : ℕ} (hn : 1 ≤ n) :
    (binarySetFamily n).card = 2 ^ (n - 1) := by
  rw [← Finset.card_image_of_injective _ setPolynomial_injective,
    binarySetFamily_image_setPolynomial hn, card_binaryFamily]

end OdlyzkoPoonen
