import OdlyzkoPoonen.Polynomial.FrobeniusCongruence
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Divisibility of monic polynomial resultants

Padding the degree of the second polynomial does not change a monic resultant.
This permits a polynomial remainder modulo the first input without a degree
restriction on that remainder. Frobenius then gives the full prime power
`p ^ degree J` in the resultant of `J(X)` and `J(X^p)`.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma resultant_map_injective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (f g : R[X]) :
    resultant (f.map φ) (g.map φ) = φ (resultant f g) := by
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map]

lemma monic_resultant_right_degree {R : Type*} [CommRing R] {f : R[X]}
    (hf : f.Monic) (g : R[X]) {n : ℕ} (hn : g.natDegree ≤ n) :
    resultant f g f.natDegree n = resultant f g := by
  have he : n = g.natDegree + (n - g.natDegree) := by omega
  rw [he, resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp [hf.coeff_natDegree]

lemma pow_dvd_resultant_of_C_dvd_sub_mul {R : Type*} [CommRing R]
    {f g h : R[X]} (hf : f.Monic) {c : R} (hc : C c ∣ g - f * h) :
    c ^ f.natDegree ∣ resultant f g := by
  let N := g.natDegree + (h.natDegree + f.natDegree)
  have hpad := monic_resultant_right_degree hf g (n := N) (by dsimp [N]; omega)
  have he := resultant_add_mul_right f (g - f * h) h f.natDegree N
    (by dsimp [N]; omega) le_rfl
  rw [sub_add_cancel] at he
  rw [← hpad, he]
  obtain ⟨v, hv⟩ := hc
  rw [hv, resultant_C_mul_right]
  exact dvd_mul_right _ _

lemma prime_pow_degree_dvd_resultant_comp_X_pow {J : ℤ[X]} (hJ : J.Monic)
    {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ^ J.natDegree ∣ resultant J (J.comp (X ^ p)) := by
  apply pow_dvd_resultant_of_C_dvd_sub_mul (h := J ^ (p - 1)) hJ
  have he : J * J ^ (p - 1) = J ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le]
  rw [he]
  exact prime_C_dvd_comp_X_pow_sub_pow J hp

end OdlyzkoPoonen
