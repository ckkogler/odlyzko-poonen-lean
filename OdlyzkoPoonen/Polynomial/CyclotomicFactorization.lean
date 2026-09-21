import OdlyzkoPoonen.Polynomial.CyclotomicDivisors
import OdlyzkoPoonen.Polynomial.MonicIrreducibleDivisor

/-!
# Splitting off cyclotomic factors with multiplicity

A cyclotomic product is an actual finite product of positive-order cyclotomic
polynomials. Repeated orders and the empty product are allowed. Every monic
integer polynomial splits into such a product and a monic polynomial without
cyclotomic divisors; neither a unit remainder nor repeated factors are discarded.
-/

namespace OdlyzkoPoonen
open Polynomial

def IsCyclotomicProduct (P : ℤ[X]) : Prop :=
  ∃ ks : List ℕ, (∀ k ∈ ks, 0 < k) ∧ P = (ks.map (fun k ↦ cyclotomic k ℤ)).prod

lemma isCyclotomicProduct_one : IsCyclotomicProduct 1 := by
  exact ⟨[], by simp, by simp⟩

lemma IsCyclotomicProduct.monic {P : ℤ[X]} (h : IsCyclotomicProduct P) : P.Monic := by
  obtain ⟨ks, hks, rfl⟩ := h
  clear hks
  induction ks with
  | nil => simp
  | cons k ks ih => simpa only [List.map_cons, List.prod_cons] using
      (cyclotomic.monic k ℤ).mul ih

lemma IsCyclotomicProduct.cyclotomic_mul {P : ℤ[X]} (h : IsCyclotomicProduct P)
    {k : ℕ} (hk : 0 < k) : IsCyclotomicProduct (cyclotomic k ℤ * P) := by
  obtain ⟨ks, hks, rfl⟩ := h
  refine ⟨k :: ks, ?_, by simp⟩
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact hk
  · exact hks j hj

lemma IsCyclotomicProduct.mul {P Q : ℤ[X]} (hP : IsCyclotomicProduct P)
    (hQ : IsCyclotomicProduct Q) : IsCyclotomicProduct (P * Q) := by
  obtain ⟨ps, hps, rfl⟩ := hP
  obtain ⟨qs, hqs, rfl⟩ := hQ
  refine ⟨ps ++ qs, ?_, by simp⟩
  intro k hk
  exact (List.mem_append.mp hk).elim (hps k) (hqs k)

lemma exists_cyclotomic_factorization {P : ℤ[X]} (hP : P.Monic) :
    ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
      R.Monic ∧ ¬ HasCyclotomicDivisor R := by
  suffices h : ∀ n : ℕ, ∀ P : ℤ[X], P.natDegree = n → P.Monic →
      ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
        R.Monic ∧ ¬ HasCyclotomicDivisor R from h _ P rfl hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hdeg hmonic
    by_cases hc : HasCyclotomicDivisor P
    · obtain ⟨k, hk, R, hR⟩ := hc
      have hm : R.Monic := (cyclotomic.monic k ℤ).of_mul_monic_left (hR ▸ hmonic)
      have hd : R.natDegree < n := by
        have hd := congrArg Polynomial.natDegree hR
        rw [natDegree_mul (cyclotomic_ne_zero k ℤ) hm.ne_zero,
          natDegree_cyclotomic, hdeg] at hd
        have hp := Nat.totient_pos.mpr hk
        omega
      obtain ⟨Q, T, hQT, hQ, hT, hcyc⟩ := ih R.natDegree hd R rfl hm
      refine ⟨cyclotomic k ℤ * Q, T, ?_, hQ.cyclotomic_mul hk, hT, hcyc⟩
      rw [hR, hQT, mul_assoc]
    · exact ⟨1, P, by simp, isCyclotomicProduct_one, hmonic, hc⟩

lemma exists_noncyclotomic_irreducible_divisor_of_not_product {P : ℤ[X]}
    (hP : P.Monic) (hnot : ¬ IsCyclotomicProduct P) :
    ∃ J : ℤ[X], J.Monic ∧ Irreducible (J.map (Int.castRingHom ℚ)) ∧
      ¬ HasCyclotomicDivisor J ∧ J ∣ P := by
  obtain ⟨Q, R, hQR, hQ, hR, hcyc⟩ := exists_cyclotomic_factorization hP
  have hne : R ≠ 1 := by
    intro h
    apply hnot
    have he : P = Q := by simpa [h] using hQR
    rw [he]
    exact hQ
  have hd : 0 < R.natDegree := by
    by_contra h
    exact hne (hR.natDegree_eq_zero.mp (by omega))
  obtain ⟨J, hJ, hirr, hJR⟩ := exists_monic_rational_irreducible_divisor hR hd
  refine ⟨J, hJ, hirr, fun h ↦ hcyc (h.of_dvd hJR), ?_⟩
  rw [hQR]
  exact hJR.trans (dvd_mul_left R Q)

end OdlyzkoPoonen
