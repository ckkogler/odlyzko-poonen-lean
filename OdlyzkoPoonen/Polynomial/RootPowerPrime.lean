import OdlyzkoPoonen.Polynomial.RootRatioOrders
import OdlyzkoPoonen.Arithmetic.PrimeIntervalGrowth

/-!
# A prime which separates powers of all polynomial roots

If every prime in a finite set identifies two distinct roots of an irreducible
polynomial, the product of those primes occurs as the order of a root ratio.
The bound on such orders contradicts a product larger than twice degree^4.
The exponential prime-interval estimate then gives a prime of logarithmic size.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma exists_prime_separating_root_powers_of_product_lt {K : Type*}
    [Field K] [CharZero K] [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hne : (P.rootSet K).Nonempty) (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hlarge : 2 * P.natDegree ^ 4 < ∏ p ∈ t, p) :
    ∃ p ∈ t, Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K) := by
  classical
  by_contra! hbad
  have horder : HasRootRatioOrder P K (∏ p ∈ t, p) :=
    hasRootRatioOrder_prod_primes hmonic hirr hconst hne t hprime
      (fun p hp ↦ prime_bad_power_hasRootRatioOrder hconst (hprime p hp) (hbad p hp))
  obtain ⟨z, hz, hprim⟩ := horder
  have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)
  exact (not_lt_of_ge (order_le_two_degree_four_of_primitive_root_ratio hpos hz hprim)) hlarge

lemma exists_prime_in_interval_separating_root_powers {K : Type*}
    [Field K] [CharZero K] [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hne : (P.rootSet K).Nonempty) {a b : ℕ}
    (hlarge : 2 * P.natDegree ^ 4 < primeIntervalProduct a b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b ∧
      Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K) := by
  obtain ⟨p, hp, hinj⟩ := exists_prime_separating_root_powers_of_product_lt
    hmonic hirr hconst hne (primesInInterval a b)
    (fun p hp ↦ (mem_primesInInterval.mp hp).1) hlarge
  exact ⟨p, (mem_primesInInterval.mp hp).1, (mem_primesInInterval.mp hp).2.1,
    (mem_primesInInterval.mp hp).2.2, hinj⟩

lemma exists_prime_separating_root_powers_of_log_lt {K : Type*}
    [Field K] [CharZero K] [Normal ℚ K] {P : ℚ[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0)
    (hsplit : (P.map (algebraMap ℚ K)).Splits) {n : ℕ}
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (2 * (P.natDegree : ℝ) ^ 4) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧
      Set.InjOn (fun x : K ↦ x ^ p) (P.rootSet K) := by
  apply exists_prime_in_interval_separating_root_powers hmonic hirr hconst
    (rootSet_nonempty_of_splits_of_irreducible hmonic hirr hsplit)
  have hd : (0 : ℝ) < (P.natDegree : ℝ) := Nat.cast_pos.mpr hirr.natDegree_pos
  have hlt : 2 * (P.natDegree : ℝ) ^ 4 < (primeIntervalProduct n (8 * n) : ℝ) := by
    calc
      _ = Real.exp (Real.log (2 * (P.natDegree : ℝ) ^ 4)) :=
        (Real.exp_log (by positivity)).symm
      _ < Real.exp (n : ℝ) := Real.exp_lt_exp.mpr hlog
      _ ≤ _ := hgrowth
  exact_mod_cast hlt

end OdlyzkoPoonen
