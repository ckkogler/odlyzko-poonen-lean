import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Products of distinct cyclotomic divisors

Finite intersections of cyclotomic divisibility events are divisibility by a
single monic product. The proof uses relative primality over the integers.
Any common multiple of the orders gives a period, and exclusion of order one
also gives divisibility by the geometric sum.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

noncomputable def cyclotomicProduct (s : Finset ℕ) : ℤ[X] :=
  ∏ k ∈ s, cyclotomic k ℤ

lemma cyclotomicProduct_monic (s : Finset ℕ) : (cyclotomicProduct s).Monic :=
  monic_prod_of_monic _ _ (fun k _ ↦ cyclotomic.monic k ℤ)

lemma cyclotomicProduct_natDegree (s : Finset ℕ) :
    (cyclotomicProduct s).natDegree = ∑ k ∈ s, k.totient := by
  rw [cyclotomicProduct, natDegree_prod_of_monic s (f := fun k ↦ cyclotomic k ℤ) (fun k _ ↦ cyclotomic.monic k ℤ)]
  simp only [natDegree_cyclotomic]

lemma cyclotomic_isRelPrime_int {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (hkl : k ≠ l) :
    IsRelPrime (cyclotomic k ℤ) (cyclotomic l ℤ) := by
  apply (cyclotomic.irreducible hk).isRelPrime_iff_not_dvd.mpr
  intro hd
  apply hkl
  apply cyclotomic_injective (R := ℤ)
  exact eq_of_monic_of_associated (cyclotomic.monic k ℤ) (cyclotomic.monic l ℤ)
    ((cyclotomic.irreducible hk).associated_of_dvd (cyclotomic.irreducible hl) hd)

/-- An intersection is exactly divisibility by the squarefree product. -/
theorem cyclotomicProduct_dvd_iff {s : Finset ℕ} (hs : ∀ k ∈ s, 0 < k) (p : ℤ[X]) :
    cyclotomicProduct s ∣ p ↔ ∀ k ∈ s, cyclotomic k ℤ ∣ p := by
  constructor
  · intro h k hk
    exact (Finset.dvd_prod_of_mem (fun k ↦ cyclotomic k ℤ) hk).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro k hk l hl hkl
    exact cyclotomic_isRelPrime_int (hs k hk) (hs l hl) hkl

lemma cyclotomicProduct_dvd_X_pow_sub_one {s : Finset ℕ} {l : ℕ}
    (hl : 0 < l) (horders : ∀ k ∈ s, k ∣ l) :
    cyclotomicProduct s ∣ X ^ l - 1 := by
  rw [← prod_cyclotomic_eq_X_pow_sub_one hl ℤ]
  apply Finset.prod_dvd_prod_of_subset
  intro k hk
  exact Nat.mem_divisors.mpr ⟨horders k hk, hl.ne'⟩

lemma cyclotomicProduct_dvd_geom_sum {s : Finset ℕ} {l : ℕ}
    (hl : 0 < l) (horders : ∀ k ∈ s, k ∣ l) (hone : 1 ∉ s) :
    cyclotomicProduct s ∣ ∑ j ∈ Finset.range l, (X : ℤ[X]) ^ j := by
  rw [← prod_cyclotomic_eq_geom_sum hl ℤ]
  apply Finset.prod_dvd_prod_of_subset
  intro k hk
  apply Finset.mem_erase.mpr
  refine ⟨?_, Nat.mem_divisors.mpr ⟨horders k hk, hl.ne'⟩⟩
  intro h
  subst k
  exact hone hk

lemma cyclotomicProduct_common_period {s : Finset ℕ} (hs : ∀ k ∈ s, 0 < k) :
    0 < ∏ k ∈ s, k ∧ cyclotomicProduct s ∣ X ^ (∏ k ∈ s, k) - 1 := by
  have hp : 0 < ∏ k ∈ s, k := Finset.prod_pos hs
  exact ⟨hp, cyclotomicProduct_dvd_X_pow_sub_one hp
    (fun k hk ↦ Finset.dvd_prod_of_mem (fun k ↦ k) hk)⟩

end OdlyzkoPoonen
