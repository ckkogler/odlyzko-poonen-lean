import OdlyzkoPoonen.FiniteField.EndpointFamily

/-!
# Counting endpoint polynomials divisible by a fixed factor

Every multiple of a fixed endpoint-one polynomial is the image of its quotient.
The quotient has the complementary degree and constant coefficient one. Counting
this actual finite family bounds divisibility without an independence assumption.
The case of equal degrees includes the constant quotient, and a factor of larger
degree cannot divide any member of the target family.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

lemma HasF2Endpoints.not_dvd_of_degree_lt {n h : ℕ} {p J : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hJ : HasF2Endpoints h J) (hnh : n < h) : ¬ J ∣ p := by
  intro hdvd
  have hle := natDegree_le_of_dvd hdvd hp.monic.ne_zero
  rw [hp.degree, hJ.degree] at hle
  omega

lemma HasF2Endpoints.exists_endpoint_quotient {n h : ℕ} {p J : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hJ : HasF2Endpoints h J) (hdvd : J ∣ p) :
    ∃ q : (ZMod 2)[X], HasF2Endpoints (n - h) q ∧ p = J * q := by
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨_, hQ, hdeg⟩ := hp.factor_endpoints hq
  refine ⟨q, ⟨hQ.monic, ?_, hQ.constant⟩, hq⟩
  rw [hJ.degree] at hdeg
  omega

lemma card_endpoint_multiples_le {n h : ℕ} {J : (ZMod 2)[X]}
    (hJ : HasF2Endpoints h J) :
    ((f2EndpointFamily n).filter (fun p ↦ J ∣ p)).card ≤ 2 ^ (n - h) := by
  have hsub : (f2EndpointFamily n).filter (fun p ↦ J ∣ p) ⊆
      (f2EndpointFamily (n - h)).image (fun q ↦ J * q) := by
    intro p hp
    obtain ⟨hp, hdvd⟩ := Finset.mem_filter.mp hp
    obtain ⟨q, hq, heq⟩ := (mem_f2EndpointFamily_iff.mp hp).exists_endpoint_quotient hJ hdvd
    exact Finset.mem_image.mpr ⟨q, mem_f2EndpointFamily_iff.mpr hq, heq.symm⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (card_f2EndpointFamily_le (n - h)))

lemma f2Probability_divisible_eq_zero {n h : ℕ} {J : (ZMod 2)[X]}
    (hn : 1 ≤ n) (hJ : HasF2Endpoints h J) (hnh : n < h) :
    f2Probability (n - 1) (fun p ↦ J ∣ p) = 0 := by
  have hf : (f2Family (n - 1)).filter (fun p ↦ J ∣ p) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp, hdvd⟩ := Finset.mem_filter.mp hp
    have hep := mem_f2Family_iff.mp hp
    rw [Nat.sub_add_cancel hn] at hep
    exact hep.not_dvd_of_degree_lt hJ hnh hdvd
  rw [f2Probability_eq_count, hf, Finset.card_empty, Nat.cast_zero, zero_div]

lemma f2Probability_divisible_le {n h : ℕ} {J : (ZMod 2)[X]}
    (hn : 1 ≤ n) (hJ : HasF2Endpoints h J) :
    f2Probability (n - 1) (fun p ↦ J ∣ p) ≤ 2 / (2 : ℝ) ^ h := by
  by_cases hhn : h ≤ n
  · have hc := card_endpoint_multiples_le (n := n) hJ
    have hn0 : n ≠ 0 := by omega
    simp only [f2EndpointFamily, ite_eq_right hn0] at hc
    rw [f2Probability_eq_count]
    calc
      _ ≤ (2 : ℝ) ^ (n - h) / 2 ^ (n - 1) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = 2 / (2 : ℝ) ^ h := by
        apply (div_eq_div_iff (by positivity) (by positivity)).2
        calc
          _ = (2 : ℝ) ^ n := by rw [← pow_add, Nat.sub_add_cancel hhn]
          _ = 2 * (2 : ℝ) ^ (n - 1) := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hn]
  · rw [f2Probability_divisible_eq_zero hn hJ (by omega)]
    positivity

end OdlyzkoPoonen
