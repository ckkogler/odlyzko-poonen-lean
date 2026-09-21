import OdlyzkoPoonen.Polynomial.MonicIrreducibleDivisor
import Mathlib.Data.Finset.Preimage

/-!
# A finite family of monic irreducible integer divisors

For every nonzero integer polynomial, its monic rationally irreducible integer
divisors form a finite family of size at most its degree. The ambient polynomial
need not be monic. This allows a family selected after observing a reciprocal
sum, whose leading coefficient is two.
-/

namespace OdlyzkoPoonen
open Polynomial UniqueFactorizationMonoid
open scoped Classical

lemma normalizedFactors_card_le_natDegree (P : ℚ[X]) :
    (normalizedFactors P).card ≤ P.natDegree := by
  by_cases hP : P = 0
  · simp [hP]
  have hsum (s : Multiset ℚ[X]) (h : ∀ f ∈ s, 1 ≤ f.natDegree) :
      s.card ≤ (s.map Polynomial.natDegree).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons f s ih =>
      have hf := h f (by simp)
      have hs := ih (fun g hg ↦ h g (by simp [hg]))
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      omega
  have h := hsum (normalizedFactors P)
    (fun f hf ↦ (irreducible_of_normalized_factor f hf).natDegree_pos)
  rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors P),
    prod_normalizedFactors_eq hP, natDegree_normalize] at h
  exact h

noncomputable def monicIrreducibleDivisorFamily (S : ℤ[X]) : Finset ℤ[X] :=
  (normalizedFactors (S.map (Int.castRingHom ℚ))).toFinset.preimage
    (Polynomial.map (Int.castRingHom ℚ))
    (Polynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective :
      Function.Injective (Int.castRingHom ℚ))).injOn

lemma mem_monicIrreducibleDivisorFamily {S J : ℤ[X]} (hS : S ≠ 0) :
    J ∈ monicIrreducibleDivisorFamily S ↔
      J.Monic ∧ Irreducible (J.map (Int.castRingHom ℚ)) ∧ J ∣ S := by
  have hinj := Polynomial.map_injective (Int.castRingHom ℚ) (Int.cast_injective :
    Function.Injective (Int.castRingHom ℚ))
  have hmap : S.map (Int.castRingHom ℚ) ≠ 0 := by
    intro h
    apply hS
    apply hinj
    simpa using h
  rw [monicIrreducibleDivisorFamily, Finset.mem_preimage, Multiset.mem_toFinset,
    Polynomial.mem_normalizedFactors_iff hmap]
  constructor
  · rintro ⟨hirr, hm, hd⟩
    have hJ : J.Monic := (Function.Injective.monic_map_iff
      (Int.cast_injective : Function.Injective (Int.castRingHom ℚ))).mpr hm
    exact ⟨hJ, hirr,
      (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hJ.isPrimitive).mpr hd⟩
  · rintro ⟨hm, hirr, hd⟩
    exact ⟨hirr, hm.map _, Polynomial.map_dvd _ hd⟩

lemma monicIrreducibleDivisorFamily_card_le (S : ℤ[X]) :
    (monicIrreducibleDivisorFamily S).card ≤ S.natDegree := by
  calc
    _ ≤ (normalizedFactors (S.map (Int.castRingHom ℚ))).toFinset.card := by
      rw [monicIrreducibleDivisorFamily, Finset.card_preimage]
      exact Finset.card_filter_le _ _
    _ ≤ (normalizedFactors (S.map (Int.castRingHom ℚ))).card := Multiset.toFinset_card_le _
    _ ≤ (S.map (Int.castRingHom ℚ)).natDegree := normalizedFactors_card_le_natDegree _
    _ = _ := natDegree_map_eq_of_injective (Int.cast_injective :
      Function.Injective (Int.castRingHom ℚ)) _

end OdlyzkoPoonen
