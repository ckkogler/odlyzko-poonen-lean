import OdlyzkoPoonen.Asymptotics.CyclotomicTruncation
import OdlyzkoPoonen.Asymptotics.ReducibleNoncyclotomic

/-!
# Finite cyclotomic approximation to reducibility

At any fixed inverse-polynomial accuracy, reducibility can be replaced by a
union over a fixed finite collection of cyclotomic divisibility events. Both
the degree threshold and the finite set of orders are independent of the
random polynomial's degree.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped Classical

/-- A cyclotomic divisor whose positive degree is below `D`. -/
def HasBoundedDegreeCyclotomicDivisor (D : ℕ) (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k.totient < D ∧ cyclotomic k ℤ ∣ p

lemma hasBoundedDegreeCyclotomicDivisor_iff_finite (D : ℕ) (p : ℤ[X]) :
    HasBoundedDegreeCyclotomicDivisor D p ↔
      ∃ k ∈ Finset.Icc 1 (2 * D ^ 2), k.totient < D ∧ cyclotomic k ℤ ∣ p := by
  constructor
  · rintro ⟨k, hk, hd, hp⟩
    have hbound : k ≤ 2 * D ^ 2 := by
      apply (order_le_two_totient_sq k).trans
      gcongr
    exact ⟨k, Finset.mem_Icc.mpr ⟨hk, hbound⟩, hd, hp⟩
  · rintro ⟨k, hk, hd, hp⟩
    exact ⟨k, (Finset.mem_Icc.mp hk).1, hd, hp⟩

lemma HasBinaryEndpoints.reducible_of_bounded_cyclotomic {n D : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : D ≤ n)
    (hdiv : HasBoundedDegreeCyclotomicDivisor D p) : ReducibleOverRat p := by
  apply (monic_reducibleOverRat_iff hp.monic).mpr
  intro hi
  obtain ⟨k, hk, hD, hd⟩ := hdiv
  rcases hi.dvd_iff.mp hd with hu | ha
  · have hz := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_cyclotomic] at hz
    have := Nat.totient_pos.mpr hk
    omega
  · have hle := natDegree_le_of_dvd ha.dvd (cyclotomic_ne_zero k ℤ)
    rw [hp.degree, natDegree_cyclotomic] at hle
    omega

lemma reducible_sub_bounded_cyclotomic_probability_eq {n D : ℕ}
    (hn : 1 ≤ n) (hD : D ≤ n) :
    binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor D) =
    binaryProbability (n - 1)
      (fun p ↦ ReducibleOverRat p ∧ ¬ HasBoundedDegreeCyclotomicDivisor D p) := by
  apply uniformProbability_sub_of_imp
  intro w hw
  have hp := wordPolynomial_endpoints w
  rw [Nat.sub_add_cancel hn] at hp
  exact hp.reducible_of_bounded_cyclotomic hD hw

lemma reducible_sub_bounded_cyclotomic_probability_le {n D : ℕ}
    (hn : 1 ≤ n) (hD : D ≤ n) :
    binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor D) ≤
    binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) +
      binaryProbability (n - 1)
        (fun p ↦ ∃ k, D ≤ k.totient ∧ cyclotomic k ℤ ∣ p) := by
  rw [reducible_sub_bounded_cyclotomic_probability_eq hn hD]
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦
        (ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) ∨
        (∃ k, D ≤ k.totient ∧ cyclotomic k ℤ ∣ p)) := by
      apply uniformProbability_mono
      intro w hw
      by_cases hc : HasCyclotomicDivisor (wordPolynomial w)
      · obtain ⟨k, hk, hd⟩ := hc
        apply Or.inr
        refine ⟨k, ?_, hd⟩
        by_contra h
        exact hw.2 ⟨k, hk, by omega, hd⟩
      · exact Or.inl ⟨hw.1, hc⟩
    _ ≤ _ := binaryProbability_or_le_add _ _ _

/-- A fixed finite union approximates reducibility to any prescribed natural
inverse power. No approximation theorem for the individual events is assumed. -/
theorem binaryProbability_reducible_finite_cyclotomic_approximation
    (R : ℕ) (hR : 1 ≤ R) :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor (2 * R + 1)))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  have hnoncyc : (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
    have hpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast] using
      binaryProbability_reducible_noncyclotomic_isBigO (R : ℝ) hpos
  have h := hnoncyc.add (binaryProbability_cyclotomic_degree_tail_isBigO R)
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop (2 * R + 1)] with n hn
  have hn1 : 1 ≤ n := by omega
  have he0 : 0 ≤ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor (2 * R + 1)) := by
    rw [reducible_sub_bounded_cyclotomic_probability_eq hn1 hn]
    exact uniformProbability_nonneg _
  have hs0 : 0 ≤ binaryProbability (n - 1)
      (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) +
      binaryProbability (n - 1)
        (fun p ↦ ∃ k, 2 * R + 1 ≤ k.totient ∧ cyclotomic k ℤ ∣ p) :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he0, abs_of_nonneg hs0]
    using reducible_sub_bounded_cyclotomic_probability_le hn1 hn

end OdlyzkoPoonen
