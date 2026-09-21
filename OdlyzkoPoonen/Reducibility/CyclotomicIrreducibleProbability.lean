import OdlyzkoPoonen.Reducibility.CyclotomicCutoffProbability
import OdlyzkoPoonen.Analysis.CyclotomicCutoffScales

/-!
# One irreducible noncyclotomic factor with high probability

With logarithmic exponential probability, a binary endpoint polynomial is a
cyclotomic product times one irreducible noncyclotomic integer polynomial.
With square-root exponential probability, the whole cyclotomic part has degree
at most the square root of the ambient degree. The same absolute positive
constants work in both assertions, for every degree at least three.
-/

namespace OdlyzkoPoonen
open Polynomial

def HasIrreducibleNoncyclotomicPartWithDegree (B : ℝ) (P : ℤ[X]) : Prop :=
  ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
    Irreducible R ∧ ¬ HasCyclotomicDivisor R ∧ (Q.natDegree : ℝ) ≤ B

lemma HasIrreducibleNoncyclotomicPartBelow.sqrt_degree {n : ℕ} {P : ℤ[X]}
    (h : HasIrreducibleNoncyclotomicPartBelow (⌊Real.sqrt (n : ℝ)⌋₊ + 1) P) :
    HasIrreducibleNoncyclotomicPartWithDegree (Real.sqrt (n : ℝ)) P := by
  obtain ⟨Q, R, hPR, hQ, hR, hcyc, hd⟩ := h
  exact ⟨Q, R, hPR, hQ, hR, hcyc, nat_degree_le_sqrt_of_lt_cutoff hd⟩

theorem cyclotomic_irreducible_factorization_probability :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      (1 - C * Real.exp (-c * n / Real.log (n : ℝ) ^ 4) ≤
        binaryProbability (n - 1) HasIrreducibleNoncyclotomicPart) ∧
      (1 - C * Real.exp (-c * Real.sqrt (n : ℝ)) ≤
        binaryProbability (n - 1)
          (HasIrreducibleNoncyclotomicPartWithDegree (Real.sqrt (n : ℝ)))) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hcut⟩ := cyclotomic_irreducible_factorization_cutoff_probability
  let d := Real.log 2 / 2
  have hd : 0 < d := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  let c := min c₀ d
  have hc : 0 < c := lt_min hc₀ hd
  have hcc : c ≤ c₀ := min_le_left _ _
  have hcd : c ≤ d := min_le_right _ _
  obtain ⟨N, hN, hscale⟩ := exists_threshold_logarithmic_rate_ge_sqrt
  let f₁ : ℕ → ℝ := fun n ↦ 1 - binaryProbability (n - 1) HasIrreducibleNoncyclotomicPart
  let f₂ : ℕ → ℝ := fun n ↦ 1 - binaryProbability (n - 1)
    (HasIrreducibleNoncyclotomicPartWithDegree (Real.sqrt (n : ℝ)))
  have hunit₁ : ∀ n, f₁ n ≤ 1 := by
    intro n
    have h := uniformProbability_nonneg (fun w : Fin (n - 1) → Bool ↦
      HasIrreducibleNoncyclotomicPart (wordPolynomial w))
    dsimp [f₁, binaryProbability]
    linarith
  have hunit₂ : ∀ n, f₂ n ≤ 1 := by
    intro n
    have h := uniformProbability_nonneg (fun w : Fin (n - 1) → Bool ↦
      HasIrreducibleNoncyclotomicPartWithDegree (Real.sqrt (n : ℝ)) (wordPolynomial w))
    dsimp [f₂, binaryProbability]
    linarith
  have hfirst : ∀ n, N ≤ n → f₁ n ≤ (C₀ + 8) * Real.exp (-(c * n / Real.log (n : ℝ) ^ 4)) := by
    intro n hn
    have hn3 := hN.trans hn
    obtain ⟨hlog, _⟩ := hscale n hn
    have hcutn := hcut n n hn3 (by omega) le_rfl
    have hmono : binaryProbability (n - 1) (HasIrreducibleNoncyclotomicPartBelow n) ≤
        binaryProbability (n - 1) HasIrreducibleNoncyclotomicPart :=
      uniformProbability_mono (fun _ h ↦ h.forget)
    have hexp := logarithmic_exp_antitone_rate hcc n
    have hrate : c * n / Real.log (n : ℝ) ^ 4 ≤ d * n := by
      calc
        _ ≤ c * n := div_le_self (by positivity) (one_le_pow₀ hlog)
        _ ≤ _ := mul_le_mul_of_nonneg_right hcd (Nat.cast_nonneg n)
    have htail : (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ Real.exp (-(c * n / Real.log (n : ℝ) ^ 4)) :=
      (reciprocal_tail_le_exp (L := n) (x := (n : ℝ)) le_rfl).trans (by
        simpa only [d, neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hrate))
    change f₁ n ≤ _
    dsimp [f₁]
    simp only [neg_div, neg_mul] at hexp hcutn htail
    nlinarith [mul_le_mul_of_nonneg_left hexp hC₀.le]
  have hsecond : ∀ n, N ≤ n → f₂ n ≤ (C₀ + 8) * Real.exp (-(c * Real.sqrt (n : ℝ))) := by
    intro n hn
    have hn3 := hN.trans hn
    obtain ⟨_, hlograte⟩ := hscale n hn
    obtain ⟨hL1, hLn, hLs⟩ := sqrt_degree_cutoff hn3
    have hcutn := hcut n (⌊Real.sqrt (n : ℝ)⌋₊ + 1) hn3 hL1 hLn
    have hmono : binaryProbability (n - 1)
        (HasIrreducibleNoncyclotomicPartBelow (⌊Real.sqrt (n : ℝ)⌋₊ + 1)) ≤
        binaryProbability (n - 1)
          (HasIrreducibleNoncyclotomicPartWithDegree (Real.sqrt (n : ℝ))) :=
      uniformProbability_mono (fun _ h ↦ h.sqrt_degree)
    have hrate : c * Real.sqrt (n : ℝ) ≤ c₀ * n / Real.log (n : ℝ) ^ 4 := by
      calc
        _ ≤ c * ((n : ℝ) / Real.log (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hlograte hc.le
        _ ≤ c₀ * ((n : ℝ) / Real.log (n : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right hcc (by positivity)
        _ = _ := by ring
    have hexp : Real.exp (-c₀ * n / Real.log (n : ℝ) ^ 4) ≤
        Real.exp (-(c * Real.sqrt (n : ℝ))) := by
      simpa only [neg_div, neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hrate)
    have htail : (2 : ℝ) ^ (-((⌊Real.sqrt (n : ℝ)⌋₊ + 1 : ℕ) : ℝ) / 2) ≤
        Real.exp (-(c * Real.sqrt (n : ℝ))) := (reciprocal_tail_le_exp hLs.le).trans (by
      simpa only [d, neg_mul] using Real.exp_le_exp.mpr
        (neg_le_neg (mul_le_mul_of_nonneg_right hcd (Real.sqrt_nonneg (n : ℝ)))))
    dsimp [f₂]
    nlinarith [mul_le_mul_of_nonneg_left hexp hC₀.le]
  obtain ⟨D₁, hD₁, hb₁⟩ := extend_scaled_exponential_bound (by positivity : 0 < C₀ + 8) hunit₁ hfirst
  obtain ⟨D₂, hD₂, hb₂⟩ := extend_scaled_exponential_bound (by positivity : 0 < C₀ + 8) hunit₂ hsecond
  refine ⟨c, max D₁ D₂, hc, hD₁.trans_le (le_max_left _ _), ?_⟩
  intro n _
  constructor
  · have h := (hb₁ n).trans (mul_le_mul_of_nonneg_right (le_max_left D₁ D₂) (Real.exp_pos _).le)
    dsimp [f₁] at h
    simp only [neg_div, neg_mul]
    linarith
  · have h := (hb₂ n).trans (mul_le_mul_of_nonneg_right (le_max_right D₁ D₂) (Real.exp_pos _).le)
    dsimp [f₂] at h
    simp only [neg_mul]
    linarith

end OdlyzkoPoonen
