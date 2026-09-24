import OdlyzkoPoonen.Polynomial.ComplexRootPowerPrime

/-!
# A product bound for all bad root-power primes

For any finite set of primes whose power maps identify distinct roots, their
product is itself a realized root-ratio order. Counting primitive conjugates
bounds this product by twice the fourth power of the degree. The final theorem
uses the actual complex root multiset of an integer polynomial.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- The actual power map is injective on every complex root of `J`. -/
def RootPowerSeparates (J : ℤ[X]) (p : ℕ) : Prop :=
  ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
    ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p = b ^ p → a = b

lemma prod_bad_root_power_primes_le {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic) (hirr : Irreducible P)
    (hconst : P.coeff 0 ≠ 0) (hne : (P.rootSet K).Nonempty)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K)) :
    (∏ p ∈ t, p) ≤ 2 * P.natDegree ^ 4 := by
  have ho := hasRootRatioOrder_prod_primes hmonic hirr hconst hne t hprime
    (fun p hp ↦ prime_bad_power_hasRootRatioOrder hconst (hprime p hp) (hbad p hp))
  obtain ⟨z, hz, hprim⟩ := ho
  exact order_le_two_degree_four_of_primitive_root_ratio
    (Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)) hz hprim

lemma root_power_injOn_transfer {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] {P : F[X]}
    (hs : (P.map (algebraMap F K)).Splits) (j : K →ₐ[F] L) {p : ℕ}
    (hinj : Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K)) :
    Set.InjOn (fun x : L ↦ x ^ p) (P.rootSet L) := by
  have himage := hs.image_rootSet j
  intro z hz w hw he
  rw [← himage] at hz hw
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, rfl⟩ := hw
  apply congrArg j
  apply hinj ha hb
  apply j.injective
  change j (a ^ p) = j (b ^ p)
  rw [map_pow, map_pow]
  exact he

lemma prod_bad_complex_root_power_primes_le {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ Set.InjOn (fun x : ℂ ↦ x ^ p) (P.rootSet ℂ)) :
    (∏ p ∈ t, p) ≤ 2 * P.natDegree ^ 4 := by
  have : Normal ℚ P.SplittingField := by
    convert (Polynomial.SplittingField.instNormal P) using 1 <;> exact Subsingleton.elim _ _
  apply prod_bad_root_power_primes_le (K := P.SplittingField) hmonic hirr hconst
    (rootSet_nonempty_of_splits_of_irreducible hmonic hirr (SplittingField.splits P)) t hprime
  intro p hp hinj
  exact hbad p hp (root_power_injOn_transfer (SplittingField.splits P)
    (SplittingField.lift P (IsAlgClosed.splits _)) hinj)

lemma prod_bad_integer_root_power_primes_le {J : ℤ[X]} (hmonic : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ RootPowerSeparates J p) :
    (∏ p ∈ t, p) ≤ 2 * J.natDegree ^ 4 := by
  have hconstQ : (J.map (Int.castRingHom ℚ)).coeff 0 ≠ 0 := by
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ne_zero] using hconst
  have heq : (J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      J.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  have h := prod_bad_complex_root_power_primes_le (hmonic.map _) hirr hconstQ t hprime
    (fun p hp hinj ↦ hbad p hp (fun a ha b hb he ↦ hinj
      (by change a ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
          rw [heq]; exact Multiset.mem_toFinset.mpr ha)
      (by change b ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
          rw [heq]; exact Multiset.mem_toFinset.mpr hb) he))
  rwa [hmonic.natDegree_map] at h

end OdlyzkoPoonen
