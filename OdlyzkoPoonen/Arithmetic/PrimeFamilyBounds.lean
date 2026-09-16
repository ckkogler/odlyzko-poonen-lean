import OdlyzkoPoonen.Arithmetic.PrimeIntervals

/-!
# Size and logarithmic weight of finite prime families

Every subset of primes in an interval has cardinality controlled by its
logarithmic weight. Chebyshev's elementary upper bound gives an absolute
weight bound on a fixed-ratio interval; the sum of primes is bounded by the
upper endpoint times their number.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma card_mul_log_lower_le_prime_weight {a b : ℕ} (ha : 0 < a) {t : Finset ℕ}
    (ht : t ⊆ primesInInterval a b) :
    (t.card : ℝ) * Real.log (a : ℝ) ≤ ∑ p ∈ t, Real.log (p : ℝ) := by
  calc
    _ = ∑ _p ∈ t, Real.log (a : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun p hp ↦ Real.log_le_log (by exact_mod_cast ha)
      (by exact_mod_cast (mem_primesInInterval.mp (ht hp)).2.1.le))

lemma prime_weight_le_card_mul_log_upper {a b : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesInInterval a b) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ (t.card : ℝ) * Real.log (b : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ t, Real.log (b : ℝ) := Finset.sum_le_sum (fun p hp ↦
      Real.log_le_log (by exact_mod_cast (mem_primesInInterval.mp (ht hp)).1.pos)
        (by exact_mod_cast (mem_primesInInterval.mp (ht hp)).2.2))
    _ = _ := by simp

lemma sum_primes_le_card_mul_upper {a b : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesInInterval a b) :
    (∑ p ∈ t, p) ≤ t.card * b := by
  calc
    _ ≤ ∑ _p ∈ t, b := Finset.sum_le_sum (fun p hp ↦ (mem_primesInInterval.mp (ht hp)).2.2)
    _ = _ := by simp

lemma prime_weight_le_sixteen_mul {n : ℕ} {t : Finset ℕ}
    (ht : t ⊆ primesInInterval n (8 * n)) :
    (∑ p ∈ t, Real.log (p : ℝ)) ≤ 16 * (n : ℝ) := by
  have hsub : t ⊆ Nat.primesLE (8 * n) := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := mem_primesInInterval.mp (ht hp)
    exact Nat.mem_primesLE.mpr ⟨hhi, hprime⟩
  have hweight : (∑ p ∈ t, Real.log (p : ℝ)) ≤ Chebyshev.theta (8 * n : ℕ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hpt
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  have htheta := Chebyshev.theta_le_log4_mul_x (by positivity : (0 : ℝ) ≤ (8 * n : ℕ))
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num at hlog2 ⊢
    linarith
  calc
    _ ≤ Chebyshev.theta (8 * n : ℕ) := hweight
    _ ≤ Real.log 4 * (8 * n : ℕ) := htheta
    _ ≤ 2 * (8 * n : ℕ) := mul_le_mul_of_nonneg_right hlog4 (by positivity)
    _ = _ := by push_cast; ring

lemma card_prime_family_le {n : ℕ} (hn : 1 < n) {t : Finset ℕ}
    (ht : t ⊆ primesInInterval n (8 * n)) :
    (t.card : ℝ) ≤ 16 * (n : ℝ) / Real.log (n : ℝ) := by
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast hn))).mpr
  exact (card_mul_log_lower_le_prime_weight (by omega) ht).trans (prime_weight_le_sixteen_mul ht)

end OdlyzkoPoonen
