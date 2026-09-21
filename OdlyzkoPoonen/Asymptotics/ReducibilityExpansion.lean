import OdlyzkoPoonen.Asymptotics.CyclotomicUnionExpansion
import OdlyzkoPoonen.Asymptotics.SharpCyclotomicTruncation
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors

/-!
# Arbitrary-order periodic expansions of reducibility

At every fixed inverse-power accuracy, a finite cyclotomic union approximates
reducibility. Its exact inclusion-exclusion formula and lattice integral
expansions supply fixed half-power coefficients. The modulus and coefficients
may depend on the requested order, but are independent of the degree.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

/-- The finite positive orders other than one with totient below a fixed bound. -/
def smallCyclotomicOrders (D : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (2 * D ^ 2)).filter (fun k ↦ k.totient < D)

lemma smallCyclotomicOrders_ge_two {D k : ℕ} (hk : k ∈ smallCyclotomicOrders D) : 2 ≤ k :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1

lemma HasBinaryEndpoints.bounded_cyclotomic_iff_small_orders {n D : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) :
    HasBoundedDegreeCyclotomicDivisor D p ↔
      ∃ k ∈ smallCyclotomicOrders D, cyclotomic k ℤ ∣ p := by
  rw [hasBoundedDegreeCyclotomicDivisor_iff_finite]
  constructor
  · rintro ⟨k, hk, hdegree, hdiv⟩
    have hne : k ≠ 1 := by
      intro he
      subst k
      exact hp.not_cyclotomic_one_dvd hdiv
    have hlow : 2 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
    exact ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hlow, (Finset.mem_Icc.mp hk).2⟩, hdegree⟩, hdiv⟩
  · rintro ⟨k, hk, hdiv⟩
    obtain ⟨hk, hdegree⟩ := Finset.mem_filter.mp hk
    have hb := Finset.mem_Icc.mp hk
    exact ⟨k, Finset.mem_Icc.mpr ⟨by omega, hb.2⟩, hdegree, hdiv⟩

lemma binaryProbability_bounded_cyclotomic_eq_small_union (m D : ℕ) :
    binaryProbability m (HasBoundedDegreeCyclotomicDivisor D) =
      binaryProbability m (fun p ↦ ∃ k ∈ smallCyclotomicOrders D, cyclotomic k ℤ ∣ p) := by
  unfold binaryProbability
  congr 1
  funext w
  exact propext (wordPolynomial_endpoints w).bounded_cyclotomic_iff_small_orders

/-- A degree-indexed half-power expansion of reducibility to every fixed order.
The coefficient of each power depends only on a fixed residue class. -/
theorem binaryProbability_reducible_predecessor_residue_expansion (R : ℕ) (hR : 1 ≤ R) :
    ∃ q : ℕ, ∃ hq : 0 < q, ∃ c : Fin q → ℕ → ℝ,
      (∀ r, c r 0 = 0) ∧
      (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
        ∑ j ∈ Finset.range (2 * R), c ⟨(n - 1) % q, Nat.mod_lt _ hq⟩ j *
          (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
            (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
  let s := smallCyclotomicOrders (2 * R)
  let q := ∏ k ∈ s, k
  have hs : ∀ k ∈ s, 2 ≤ k := fun _ hk ↦ smallCyclotomicOrders_ge_two hk
  have hq : 0 < q := Finset.prod_pos (fun k hk ↦ lt_of_lt_of_le (by omega) (hs k hk))
  obtain ⟨c, hc0, hc⟩ := binaryProbability_cyclotomic_union_expansion s hs hq
    (fun k hk ↦ Finset.dvd_prod_of_mem (fun k ↦ k) hk) R hR
  refine ⟨2 * q, by omega, c, hc0, ?_⟩
  have ht : (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ ∃ k ∈ s, cyclotomic k ℤ ∣ p)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
    simpa only [binaryProbability_bounded_cyclotomic_eq_small_union,
      Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast] using
      binaryProbability_reducible_sharp_finite_cyclotomic_approximation R hR
  simpa only [sub_add_sub_cancel] using ht.add hc

lemma predecessor_residue_rotation {q n : ℕ} (hq : 0 < q) (hn : 1 ≤ n) :
    (n % q + q - 1) % q = (n - 1) % q := by
  calc
    _ = (n % q + (q - 1)) % q := by congr 1; omega
    _ = (n + (q - 1)) % q := by simp [Nat.add_mod]
    _ = ((n - 1) + q) % q := by congr 1; omega
    _ = _ := by simp

/-- Arbitrary-order half-power coefficients depend only on the degree modulo a fixed period. -/
theorem binaryProbability_reducible_periodic_expansion (R : ℕ) (hR : 1 ≤ R) :
    ∃ q : ℕ, ∃ hq : 0 < q, ∃ c : Fin q → ℕ → ℝ,
      (∀ r, c r 0 = 0) ∧
      (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
        ∑ j ∈ Finset.range (2 * R), c ⟨n % q, Nat.mod_lt _ hq⟩ j *
          (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
            (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
  obtain ⟨q, hq, c, hc0, hc⟩ := binaryProbability_reducible_predecessor_residue_expansion R hR
  let b : Fin q → ℕ → ℝ := fun r j ↦ c ⟨(r.val + q - 1) % q, Nat.mod_lt _ hq⟩ j
  refine ⟨q, hq, b, fun r ↦ hc0 _, ?_⟩
  apply hc.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp only [b]
  have he : (⟨(n % q + q - 1) % q, Nat.mod_lt _ hq⟩ : Fin q) =
      ⟨(n - 1) % q, Nat.mod_lt _ hq⟩ := Fin.ext (predecessor_residue_rotation hq hn)
  rw [he]

end OdlyzkoPoonen
