import OdlyzkoPoonen.Analysis.LogarithmicScale

/-!
# Numerical scales for cyclotomic degree cutoffs

The reciprocal degree tail is exponential in the cutoff. A cutoff immediately
above the square root gives the required integer degree bound, and the
logarithmic rate eventually dominates the square-root rate. A finite prefix
can always be covered by a larger constant for a function bounded by one.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology BigOperators

lemma extend_scaled_exponential_bound {f g : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hunit : ∀ n, f n ≤ 1) {N : ℕ}
    (hbound : ∀ n, N ≤ n → f n ≤ C * Real.exp (-g n)) :
    ∃ D : ℝ, 0 < D ∧ ∀ n, f n ≤ D * Real.exp (-g n) := by
  let D := C + ∑ i ∈ Finset.range N, Real.exp (g i)
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, Real.exp (g i) :=
    Finset.sum_nonneg (fun i _ ↦ (Real.exp_pos _).le)
  have hCD : C ≤ D := by dsimp [D]; linarith
  refine ⟨D, hC.trans_le hCD, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (hbound n hn).trans (mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le)
  · have hsingle : Real.exp (g n) ≤ D := by
      have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) ↦ (Real.exp_pos (g i)).le)
        (Finset.mem_range.mpr (by omega : n < N))
      dsimp [D]
      linarith
    refine (hunit n).trans ?_
    calc
      1 = Real.exp (g n) * Real.exp (-g n) := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hsingle (Real.exp_pos _).le

lemma reciprocal_tail_le_exp {L : ℕ} {x : ℝ} (hx : x ≤ (L : ℝ)) :
    (2 : ℝ) ^ (-(L : ℝ) / 2) ≤ Real.exp (-(Real.log 2 / 2) * x) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

lemma sqrt_degree_cutoff {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ + 1 ∧ ⌊Real.sqrt (n : ℝ)⌋₊ + 1 ≤ n ∧
      Real.sqrt (n : ℝ) < ((⌊Real.sqrt (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) < (n : ℝ) := by
    apply (Real.sqrt_lt' (by positivity)).mpr
    nlinarith
  have hf : ⌊Real.sqrt (n : ℝ)⌋₊ < n := (Nat.floor_lt (Real.sqrt_nonneg _)).mpr hs
  refine ⟨by omega, by omega, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.sqrt (n : ℝ))

lemma nat_degree_le_sqrt_of_lt_cutoff {n d : ℕ}
    (hd : d < ⌊Real.sqrt (n : ℝ)⌋₊ + 1) : (d : ℝ) ≤ Real.sqrt (n : ℝ) := by
  exact (show (d : ℝ) ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by exact_mod_cast (show d ≤ _ by omega)).trans
    (Nat.floor_le (Real.sqrt_nonneg _))

lemma exists_threshold_logarithmic_rate_ge_sqrt :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ Real.log (n : ℝ) ∧ Real.sqrt (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 4 := by
  have hsmall : (fun n : ℕ ↦ Real.log (n : ℝ) ^ 4) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
    have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    simpa only [Function.comp_def, Real.rpow_ofNat, ← Real.sqrt_eq_rpow] using h
  have he := hsmall.tendsto_div_nhds_zero.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  obtain ⟨N₁, _, hscale⟩ := exists_threshold_logarithmic_prime_scale 1
  refine ⟨max 3 (max N₀ N₁), le_max_left _ _, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hlog := (hscale n hn₁).1
  have hs := (div_le_iff₀ (Real.sqrt_pos.mpr hn0)).mp (hN₀ n hn₀)
  refine ⟨hlog, (le_div_iff₀ (by positivity)).mpr ?_⟩
  have heq := Real.sq_sqrt hn0.le
  have hmul := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (n : ℝ))
  nlinarith

end OdlyzkoPoonen
