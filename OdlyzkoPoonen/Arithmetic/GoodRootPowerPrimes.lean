import OdlyzkoPoonen.Polynomial.RootPowerBadPrimes
import OdlyzkoPoonen.Arithmetic.PrimeFamilyBounds

/-!
# Quantitative families of good root-power primes

Discard from an interval precisely the primes that fail to separate the actual
complex roots. Their total logarithmic weight is at most log(2*degree^4).
The proved Chebyshev interval bound therefore leaves a large weight of good
primes, with explicit upper bounds on their number and sum.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

/-- The actual primes in `(a,b]` whose power map separates every complex root. -/
def goodRootPowerPrimes (J : ℤ[X]) (a b : ℕ) : Finset ℕ :=
  (primesInInterval a b).filter (RootPowerSeparates J)

lemma mem_goodRootPowerPrimes {J : ℤ[X]} {a b p : ℕ} :
    p ∈ goodRootPowerPrimes J a b ↔
      p.Prime ∧ a < p ∧ p ≤ b ∧ RootPowerSeparates J p := by
  simp only [goodRootPowerPrimes, Finset.mem_filter, mem_primesInInterval]
  tauto

lemma goodRootPowerPrimes_subset (J : ℤ[X]) (a b : ℕ) :
    goodRootPowerPrimes J a b ⊆ primesInInterval a b := Finset.filter_subset _ _

lemma sum_log_bad_root_power_primes_le {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime)
    (hbad : ∀ p ∈ t, ¬ RootPowerSeparates J p) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ Real.log (2 * (J.natDegree : ℝ) ^ 4) := by
  have hpos : (0 : ℝ) < ((∏ p ∈ t, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun p hp ↦ (hprime p hp).pos)
  have hbound : ((∏ p ∈ t, p : ℕ) : ℝ) ≤ 2 * (J.natDegree : ℝ) ^ 4 := by
    exact_mod_cast prod_bad_integer_root_power_primes_le hJ hirr hconst t hprime hbad
  have h := Real.log_le_log hpos hbound
  rw [Nat.cast_prod, Real.log_prod (fun p hp ↦ by exact_mod_cast (hprime p hp).ne_zero)] at h
  exact h

lemma good_root_power_prime_weight_lower {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    {n : ℕ} (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ)) :
    (n : ℝ) - Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤
      ∑ p ∈ goodRootPowerPrimes J n (8 * n), Real.log (p : ℝ) := by
  have hfull : (n : ℝ) ≤ ∑ p ∈ primesInInterval n (8 * n), Real.log (p : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hgrowth
    rw [Real.log_exp, primeIntervalProduct, Nat.cast_prod,
      Real.log_prod (fun p hp ↦ by exact_mod_cast (mem_primesInInterval.mp hp).1.ne_zero)] at h
    exact h
  have hbad := sum_log_bad_root_power_primes_le hJ hirr hconst
    ((primesInInterval n (8 * n)).filter (fun p ↦ ¬ RootPowerSeparates J p))
    (fun p hp ↦ (mem_primesInInterval.mp (Finset.mem_filter.mp hp).1).1)
    (fun p hp ↦ (Finset.mem_filter.mp hp).2)
  have he := Finset.sum_filter_add_sum_filter_not (primesInInterval n (8 * n))
    (RootPowerSeparates J) (fun p ↦ Real.log (p : ℝ))
  change _ ≤ ∑ p ∈ (primesInInterval n (8 * n)).filter (RootPowerSeparates J), Real.log (p : ℝ)
  linarith

lemma card_goodRootPowerPrimes_le (J : ℤ[X]) {n : ℕ} (hn : 1 < n) :
    ((goodRootPowerPrimes J n (8 * n)).card : ℝ) ≤
      16 * (n : ℝ) / Real.log (n : ℝ) :=
  card_prime_family_le hn (goodRootPowerPrimes_subset J n (8 * n))

lemma sum_goodRootPowerPrimes_le (J : ℤ[X]) (n : ℕ) :
    (∑ p ∈ goodRootPowerPrimes J n (8 * n), p) ≤
      (goodRootPowerPrimes J n (8 * n)).card * (8 * n) :=
  sum_primes_le_card_mul_upper (goodRootPowerPrimes_subset J n (8 * n))

lemma exists_threshold_good_root_power_prime_weight :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      ∀ n : ℕ, N ≤ n → Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤ (n : ℝ) / 2 →
        (n : ℝ) / 2 ≤ ∑ p ∈ goodRootPowerPrimes J n (8 * n), Real.log (p : ℝ) := by
  obtain ⟨N, hN, hgrowth⟩ := exists_threshold_exp_le_primeIntervalProduct
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro J hJ hirr hconst n hn hlog
  have h := good_root_power_prime_weight_lower hJ hirr hconst
    (hgrowth n ((le_max_right _ _).trans hn))
  linarith

end OdlyzkoPoonen
