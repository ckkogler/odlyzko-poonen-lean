import OdlyzkoPoonen.FiniteField.AutocorrelationFactors

/-!
# Parametrizing finite-field autocorrelation companions

Equal autocorrelations of endpoint-one polynomials are parametrized as `a*b`
and `a*b.reverse`: take the gcd and use the coprime cofactor result. A nontrivial
companion forces both factors to be nonreciprocal and of positive degree.
Reversing the companion exchanges the two factors, so their degrees can be
ordered without changing the first polynomial.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma equal_autocorrelation_factorization {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G)
    (h : F * F.reverse = G * G.reverse) :
    ∃ a b : (ZMod 2)[X],
      HasF2Endpoints a.natDegree a ∧ HasF2Endpoints b.natDegree b ∧
      F = a * b ∧ G = a * b.reverse ∧ a.natDegree + b.natDegree = n := by
  obtain ⟨a, b, t, hFb, hGt, ha, hb, ht, hcop, hdegF, hdegG⟩ :=
    exists_coprime_endpoint_factors hF hG
  have hbt : t.natDegree = b.natDegree := by omega
  have ht' : HasF2Endpoints b.natDegree t := ⟨ht.monic, hbt, ht.constant⟩
  have hcancel : b * b.reverse = t * t.reverse := by
    apply cancel_common_autocorrelation_factor ha
    simpa only [← hFb, ← hGt] using h
  have hrev := coprime_equal_autocorrelation_reverse hb ht' hcop hcancel
  exact ⟨a, b, ha, hb, hFb, by simpa only [hrev] using hGt, hdegF⟩

lemma nontrivial_companion_factorization {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G)
    (h : F * F.reverse = G * G.reverse) (hne : G ≠ F) (hrev : G ≠ F.reverse) :
    ∃ (d e : ℕ) (a b : (ZMod 2)[X]),
      1 ≤ d ∧ 1 ≤ e ∧ d + e = n ∧ HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
      F = a * b ∧ G = a * b.reverse ∧ a ≠ a.reverse ∧ b ≠ b.reverse := by
  obtain ⟨a, b, ha, hb, hFb, hGb, hdeg⟩ := equal_autocorrelation_factorization hF hG h
  have hna : a ≠ a.reverse := by
    intro heq
    apply hrev
    rw [hGb, hFb, reverse_mul_of_domain, ← heq]
  have hnb : b ≠ b.reverse := by
    intro heq
    apply hne
    rw [hGb, ← heq, ← hFb]
  exact ⟨a.natDegree, b.natDegree, a, b,
    ha.degree_pos_of_nonreciprocal hna, hb.degree_pos_of_nonreciprocal hnb,
    hdeg, ha, hb, hFb, hGb, hna, hnb⟩

/-- Reversal of the companion allows the common factor to have the smaller degree. -/
lemma ordered_companion_factorization {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G)
    (h : F * F.reverse = G * G.reverse) (hne : G ≠ F) (hrev : G ≠ F.reverse) :
    ∃ (d e : ℕ) (a b : (ZMod 2)[X]),
      1 ≤ d ∧ d ≤ e ∧ d + e = n ∧ HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
      F = a * b ∧ a ≠ a.reverse ∧ b ≠ b.reverse ∧
      (G = a * b.reverse ∨ G.reverse = a * b.reverse) := by
  obtain ⟨d, e, a, b, hd, he, hdeg, ha, hb, hFb, hGb, hna, hnb⟩ :=
    nontrivial_companion_factorization hF hG h hne hrev
  by_cases hde : d ≤ e
  · exact ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hFb, hna, hnb, Or.inl hGb⟩
  · refine ⟨e, d, b, a, he, by omega, by omega, hb, ha, ?_, hnb, hna, Or.inr ?_⟩
    · simpa only [mul_comm] using hFb
    · rw [hGb, reverse_mul_of_domain, hb.reverse_reverse, mul_comm]

end OdlyzkoPoonen
