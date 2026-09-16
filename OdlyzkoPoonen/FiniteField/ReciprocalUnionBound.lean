import OdlyzkoPoonen.FiniteField.DivisorCounting
import OdlyzkoPoonen.FiniteField.ReciprocalGcd
import OdlyzkoPoonen.Probability.FiniteSetUnion

/-!
# Covering a large reciprocal gcd by finite divisor families

A large gcd with the reverse is itself a reciprocal endpoint-one divisor.
Union bounds first over the reciprocal family of each degree and then over
possible degrees reduce its probability to an explicit finite geometric sum.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

/-- Existence of an actual monic reciprocal degree-`h` divisor with constant one. -/
def HasReciprocalF2Divisor (h : ℕ) (p : (ZMod 2)[X]) : Prop :=
  ∃ J : (ZMod 2)[X], HasF2Endpoints h J ∧ J.reverse = J ∧ J ∣ p

lemma hasReciprocalF2Divisor_iff_mem {h : ℕ} {p : (ZMod 2)[X]} :
    HasReciprocalF2Divisor h p ↔
      ∃ J ∈ (f2EndpointFamily h).filter (fun J ↦ J.reverse = J), J ∣ p := by
  simp only [HasReciprocalF2Divisor, Finset.mem_filter, mem_f2EndpointFamily_iff]
  tauto

lemma f2Probability_reciprocal_divisor_le {n : ℕ} (hn : 1 ≤ n) (h : ℕ) :
    f2Probability (n - 1) (HasReciprocalF2Divisor h) ≤
      (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h) := by
  unfold f2Probability
  simp_rw [hasReciprocalF2Divisor_iff_mem]
  have hbound := uniformProbability_exists_mem_le_card_mul
    ((f2EndpointFamily h).filter (fun J ↦ J.reverse = J))
    (fun (J : (ZMod 2)[X]) (w : Fin (n - 1) → Bool) ↦ J ∣ f2WordPolynomial w)
    (2 / (2 : ℝ) ^ h) (by
      intro J hJ
      exact f2Probability_divisible_le hn
        (mem_f2EndpointFamily_iff.mp (Finset.mem_filter.mp hJ).1))
  rw [card_reciprocal_f2EndpointFamily] at hbound
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound

lemma HasF2Endpoints.exists_reciprocal_divisor_of_gcd_degree {n L : ℕ}
    {p : (ZMod 2)[X]} (hp : HasF2Endpoints n p)
    (hL : L ≤ (GCDMonoid.gcd p p.reverse).natDegree) :
    ∃ h ∈ Finset.Icc L n, HasReciprocalF2Divisor h p := by
  refine ⟨(GCDMonoid.gcd p p.reverse).natDegree,
    Finset.mem_Icc.mpr ⟨hL, hp.gcd_reverse_degree_le⟩, ?_⟩
  exact ⟨GCDMonoid.gcd p p.reverse, hp.gcd_reverse_endpoints,
    hp.gcd_reverse_reciprocal, gcd_dvd_left p p.reverse⟩

lemma f2Probability_gcd_degree_le_sum {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    f2Probability (n - 1)
      (fun p ↦ L ≤ (GCDMonoid.gcd p p.reverse).natDegree) ≤
      ∑ h ∈ Finset.Icc L n, (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h) := by
  unfold f2Probability
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ h ∈ Finset.Icc L n, HasReciprocalF2Divisor h (f2WordPolynomial w)) := by
      apply uniformProbability_mono
      intro w hw
      have hp := f2WordPolynomial_endpoints w
      rw [Nat.sub_add_cancel hn] at hp
      exact hp.exists_reciprocal_divisor_of_gcd_degree hw
    _ ≤ ∑ h ∈ Finset.Icc L n,
        uniformProbability (fun w : Fin (n - 1) → Bool ↦
          HasReciprocalF2Divisor h (f2WordPolynomial w)) :=
      uniformProbability_exists_mem_le_sum (Finset.Icc L n)
        (fun (h : ℕ) (w : Fin (n - 1) → Bool) ↦
          HasReciprocalF2Divisor h (f2WordPolynomial w))
    _ ≤ _ := Finset.sum_le_sum (fun h _ ↦ f2Probability_reciprocal_divisor_le hn h)

end OdlyzkoPoonen
