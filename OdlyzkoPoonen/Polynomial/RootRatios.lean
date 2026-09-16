import OdlyzkoPoonen.Polynomial.GaloisRoots
import OdlyzkoPoonen.Arithmetic.PrimitiveRootProducts
import OdlyzkoPoonen.Arithmetic.TotientOrder

/-!
# The finite set of ratios of polynomial roots

Galois conjugacy and the irreducibility of cyclotomic polynomials imply that,
if one primitive root of a given order occurs as a ratio, then all primitive
roots of that order occur. Counting ratios bounds its totient by the square
of the polynomial degree, and hence bounds its order by twice the fourth power.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial

/-- All quotients of two roots, as an actual finite set. -/
def polynomialRootRatios {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : F[X]) : Finset K := by
  classical
  exact ((P.aroots K).toFinset ×ˢ (P.aroots K).toFinset).image (fun ab ↦ ab.1 / ab.2)

lemma mem_polynomialRootRatios {F K : Type*} [Field F] [Field K] [Algebra F K]
    {P : F[X]} {z : K} : z ∈ polynomialRootRatios P ↔
      ∃ a ∈ P.rootSet K, ∃ b ∈ P.rootSet K, a / b = z := by
  classical
  rw [polynomialRootRatios, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, (Finset.mem_product.mp hab).1, b, (Finset.mem_product.mp hab).2, he⟩
  · rintro ⟨a, ha, b, hb, he⟩
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, he⟩

lemma card_polynomialRootRatios_le {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : F[X]) : (polynomialRootRatios (K := K) P).card ≤ P.natDegree ^ 2 := by
  classical
  have hcard : (P.aroots K).toFinset.card ≤ P.natDegree :=
    (Multiset.toFinset_card_le _).trans P.card_roots_map_le_natDegree
  calc
    _ ≤ ((P.aroots K).toFinset ×ˢ (P.aroots K).toFinset).card := Finset.card_image_le
    _ = ((P.aroots K).toFinset.card) ^ 2 := by rw [Finset.card_product]; ring
    _ ≤ _ := Nat.pow_le_pow_left hcard 2

lemma algEquiv_map_mem_polynomialRootRatios {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (σ : K ≃ₐ[F] K) {z : K}
    (hz : z ∈ polynomialRootRatios P) : σ z ∈ polynomialRootRatios P := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_polynomialRootRatios.mp hz
  exact mem_polynomialRootRatios.mpr ⟨σ a, algEquiv_map_mem_rootSet σ ha,
    σ b, algEquiv_map_mem_rootSet σ hb, (map_div₀ σ a b).symm⟩

lemma primitiveRoots_subset_polynomialRootRatios {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} {r : ℕ} (hr : 0 < r) {z : K}
    (hz : z ∈ polynomialRootRatios P) (hprim : IsPrimitiveRoot z r) :
    primitiveRoots r K ⊆ polynomialRootRatios P := by
  intro y hy
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_primitiveRoot hr hprim
    ((mem_primitiveRoots hr).mp hy)
  rw [← hσ]
  exact algEquiv_map_mem_polynomialRootRatios σ hz

lemma totient_le_degree_sq_of_primitive_root_ratio {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} {r : ℕ} (hr : 0 < r) {z : K}
    (hz : z ∈ polynomialRootRatios P) (hprim : IsPrimitiveRoot z r) :
    r.totient ≤ P.natDegree ^ 2 := by
  rw [← hprim.card_primitiveRoots]
  exact (Finset.card_le_card (primitiveRoots_subset_polynomialRootRatios hr hz hprim)).trans
    (card_polynomialRootRatios_le P)

lemma order_le_two_degree_four_of_primitive_root_ratio {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {P : ℚ[X]} {r : ℕ} (hr : 0 < r) {z : K}
    (hz : z ∈ polynomialRootRatios P) (hprim : IsPrimitiveRoot z r) :
    r ≤ 2 * P.natDegree ^ 4 := by
  have ht := totient_le_degree_sq_of_primitive_root_ratio hr hz hprim
  have hsq := Nat.pow_le_pow_left ht 2
  have ho := order_le_two_totient_sq r
  nlinarith

end OdlyzkoPoonen
