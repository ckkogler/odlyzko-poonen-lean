import OdlyzkoPoonen.Polynomial.BinarySets
import OdlyzkoPoonen.Polynomial.DifferenceMultiset
import OdlyzkoPoonen.Combinatorics.AutocorrelationCount

/-!
# Reflection of endpoint-fixed subsets

Reflecting a subset about the midpoint of its endpoint interval reverses its
binary polynomial and preserves its signed difference multiset. Exactly
`2^floor(n/2)` endpoint-fixed subsets are fixed by reflection.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

def reflectedSet (n : ℕ) (A : Finset ℕ) : Finset ℕ := A.image (fun a ↦ n - a)

lemma reflectedSet_mem_binarySetFamily {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) : reflectedSet n A ∈ binarySetFamily n := by
  obtain ⟨hbound, hzero, htop⟩ := mem_binarySetFamily_iff.mp hA
  apply mem_binarySetFamily_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Nat.sub_le _ _
  · exact Finset.mem_image.mpr ⟨n, htop, Nat.sub_self n⟩
  · exact Finset.mem_image.mpr ⟨0, hzero, Nat.sub_zero n⟩

lemma setPolynomial_reflectedSet {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) :
    setPolynomial (reflectedSet n A) = (setPolynomial A).reverse := by
  have hbound := (mem_binarySetFamily_iff.mp hA).1
  calc
    _ = ∑ a ∈ A, X ^ (n - a) := by
      unfold setPolynomial reflectedSet
      rw [Finset.sum_image]
      intro a ha b hb hab
      have ha' := hbound a ha
      have hb' := hbound b hb
      change n - a = n - b at hab
      omega
    _ = _ := by
      rw [(setPolynomial_endpoints hA).reverse_eq_sum, support_setPolynomial]

lemma reflectedSet_eq_self_iff {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) :
    reflectedSet n A = A ↔ (setPolynomial A).reverse = setPolynomial A := by
  constructor
  · intro h
    rw [← setPolynomial_reflectedSet hA, h]
  · intro h
    apply setPolynomial_injective
    rw [setPolynomial_reflectedSet hA, h]

/-- Reflection preserves every signed-difference multiplicity. -/
theorem differenceMultiset_reflectedSet {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) :
    differenceMultiset (reflectedSet n A) = differenceMultiset A := by
  have hp := setPolynomial_endpoints hA
  have hr := setPolynomial_endpoints (reflectedSet_mem_binarySetFamily hA)
  have he : autocorrelation (setPolynomial (reflectedSet n A)) =
      autocorrelation (setPolynomial A) := by
    rw [setPolynomial_reflectedSet hA]
    exact autocorrelation_reverse (by rw [hp.constant]; exact one_ne_zero)
  simpa only [support_setPolynomial] using
    (differenceMultiset_eq_iff_autocorrelation_eq hr hp).mpr he

/-- The exact number of endpoint-fixed subsets symmetric about `n/2`. -/
theorem card_reflection_fixed_binarySetFamily {n : ℕ} (hn : 1 ≤ n) :
    ((binarySetFamily n).filter (fun A ↦ reflectedSet n A = A)).card = 2 ^ (n / 2) := by
  classical
  have he : ((binarySetFamily n).filter (fun A ↦ reflectedSet n A = A)).image
      setPolynomial = (binaryFamily (n - 1)).filter (fun p ↦ p.reverse = p) := by
    rw [← binarySetFamily_image_setPolynomial hn]
    ext p
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨A, ⟨hA, hr⟩, rfl⟩
      exact ⟨⟨A, hA, rfl⟩, (reflectedSet_eq_self_iff hA).mp hr⟩
    · rintro ⟨⟨A, hA, rfl⟩, hr⟩
      exact ⟨A, ⟨hA, (reflectedSet_eq_self_iff hA).mpr hr⟩, rfl⟩
  rw [← Finset.card_image_of_injective _ setPolynomial_injective, he,
    card_reciprocal_binaryFamily, Nat.sub_add_cancel hn]

end OdlyzkoPoonen
