import OdlyzkoPoonen.Polynomial.RootRatios
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Coprime products of orders of root ratios

For an irreducible polynomial, Galois transitivity moves the numerator of
one ratio to the numerator of another. Dividing the ratios then multiplies
their orders when those orders are coprime. This proves closure under products
of any finite collection of distinct prime orders.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- Some quotient of two roots is a primitive root of the specified order. -/
def HasRootRatioOrder {F : Type*} [Field F] (P : F[X]) (K : Type*) [Field K]
    [Algebra F K] (r : ℕ) : Prop :=
  ∃ z ∈ polynomialRootRatios (K := K) P, IsPrimitiveRoot z r

lemma hasRootRatioOrder_one {F K : Type*} [Field F] [Field K] [Algebra F K]
    {P : F[X]} (hconst : P.coeff 0 ≠ 0) (hne : (P.rootSet K).Nonempty) :
    HasRootRatioOrder P K 1 := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨1, mem_polynomialRootRatios.mpr ⟨a, ha, a, ha, ?_⟩, IsPrimitiveRoot.one⟩
  exact div_self (root_ne_zero_of_constant_ne_zero hconst ha)

lemma HasRootRatioOrder.mul_of_coprime {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0) {r s : ℕ}
    (hr : HasRootRatioOrder P K r) (hs : HasRootRatioOrder P K s)
    (hrs : r.Coprime s) : HasRootRatioOrder P K (r * s) := by
  obtain ⟨z, hz, hzr⟩ := hr
  obtain ⟨w, hw, hws⟩ := hs
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polynomialRootRatios.mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_polynomialRootRatios.mp hw
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_root hmonic hirr hc ha
  have hds := algEquiv_map_mem_rootSet σ hd
  have hs' : IsPrimitiveRoot (a / σ d) s := by
    simpa only [map_div₀, hσ] using hws.map_of_injective σ.injective
  have hm := primitiveRoot_mul_of_coprime hzr.inv hs' hrs
  have ha0 := root_ne_zero_of_constant_ne_zero hconst ha
  have hb0 := root_ne_zero_of_constant_ne_zero hconst hb
  have hd0 := root_ne_zero_of_constant_ne_zero hconst hds
  have he : (a / b)⁻¹ * (a / σ d) = b / σ d := by field_simp
  rw [he] at hm
  exact ⟨b / σ d, mem_polynomialRootRatios.mpr ⟨b, hb, σ d, hds, rfl⟩, hm⟩

lemma hasRootRatioOrder_prod_primes {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hne : (P.rootSet K).Nonempty) (t : Finset ℕ)
    (hprime : ∀ p ∈ t, p.Prime) (horder : ∀ p ∈ t, HasRootRatioOrder P K p) :
    HasRootRatioOrder P K (∏ p ∈ t, p) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hasRootRatioOrder_one hconst hne
  | @insert p t hp ih =>
    rw [Finset.prod_insert hp]
    apply HasRootRatioOrder.mul_of_coprime hmonic hirr hconst
      (horder p (Finset.mem_insert_self _ _))
      (ih (fun q hq ↦ hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ horder q (Finset.mem_insert_of_mem hq)))
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes (hprime p (Finset.mem_insert_self _ _))
      (hprime q (Finset.mem_insert_of_mem hq))).mpr
    intro he
    exact hp (he ▸ hq)

lemma prime_bad_power_hasRootRatioOrder {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (hconst : P.coeff 0 ≠ 0) {p : ℕ}
    (hp : p.Prime) (hbad : ¬ Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K)) :
    HasRootRatioOrder P K p := by
  classical
  simp only [Set.InjOn, not_forall] at hbad
  obtain ⟨a, ha, b, hb, he, hne⟩ := hbad
  have hb0 := root_ne_zero_of_constant_ne_zero hconst hb
  refine ⟨a / b, mem_polynomialRootRatios.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
  apply isPrimitiveRoot_of_mem_nthRootsFinset hp
  · apply (mem_nthRootsFinset hp.pos 1).mpr
    rw [div_pow, he, div_self (pow_ne_zero _ hb0)]
  · intro h
    exact hne (((div_eq_iff hb0).mp h).trans (one_mul b))

end OdlyzkoPoonen
