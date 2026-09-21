import OdlyzkoPoonen.Probability.BitWeights
import OdlyzkoPoonen.Probability.FiniteBounds

/-!
# Exact selected-bit weights and a lower-tail estimate

For any fixed selection of independent fair bits, the mean of `t` raised to
the number of true selected bits is `((1+t)/2)^k`. At `t=1/2` this gives an
exact `(3/4)^k` factor. The same identity gives an elementary exponential
lower-tail estimate without any asymptotic concentration assumption.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

def selectedTrueCount {ι : Type*} (s : Finset ι) (w : ι → Bool) : ℕ :=
  (s.filter (fun i ↦ w i = true)).card

lemma uniformAverage_bool_product {ι : Type*} [Fintype ι]
    (f : ι → Bool → ℝ) :
    uniformAverage (fun w : ι → Bool ↦ ∏ i, f i (w i)) =
      ∏ i, (f i false + f i true) / 2 := by
  have hs := Finset.sum_prod_piFinset (ι := ι) (Finset.univ : Finset Bool) f
  rw [Fintype.piFinset_univ] at hs
  rw [uniformAverage, hs, Finset.prod_div_distrib]
  simp [add_comm]

lemma uniformAverage_selectedTrueWeight {ι : Type*} [Fintype ι]
    (s : Finset ι) (t : ℝ) :
    uniformAverage (fun w : ι → Bool ↦ t ^ selectedTrueCount s w) =
      ((1 + t) / 2) ^ s.card := by
  have hw (w : ι → Bool) : t ^ selectedTrueCount s w =
      ∏ i, if i ∈ s ∧ w i = true then t else 1 := by
    have he : s.filter (fun i ↦ w i = true) =
        Finset.univ.filter (fun i ↦ i ∈ s ∧ w i = true) := by
      ext i
      simp
    simp [selectedTrueCount, Finset.prod_ite, he]
  simp_rw [hw]
  rw [uniformAverage_bool_product (fun i b ↦ if i ∈ s ∧ b = true then t else 1)]
  calc
    _ = ∏ i, if i ∈ s then (1 + t) / 2 else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [hi]
    _ = _ := by simp [div_pow]

lemma uniformAverage_selectedTrueHalfWeight {ι : Type*} [Fintype ι]
    (s : Finset ι) :
    uniformAverage (fun w : ι → Bool ↦ (1 / 2 : ℝ) ^ selectedTrueCount s w) =
      (3 / 4 : ℝ) ^ s.card := by
  rw [uniformAverage_selectedTrueWeight]
  norm_num

lemma uniformProbability_selectedTrueCount_lower_tail {ι : Type*} [Fintype ι]
    (s : Finset ι) :
    uniformProbability (fun w : ι → Bool ↦ 4 * selectedTrueCount s w ≤ s.card) ≤
      (9 / 10 : ℝ) ^ s.card := by
  rw [uniformProbability_eq_average_indicator]
  calc
    _ ≤ uniformAverage (fun w : ι → Bool ↦
        (1 / 2 : ℝ) ^ selectedTrueCount s w * (6 / 5 : ℝ) ^ s.card) := by
      apply uniformAverage_mono
      intro w
      split_ifs with h
      · have hp : (2 : ℝ) ^ selectedTrueCount s w ≤ (6 / 5 : ℝ) ^ s.card := by
          calc
            _ ≤ ((6 / 5 : ℝ) ^ 4) ^ selectedTrueCount s w :=
              pow_le_pow_left₀ (by norm_num) (by norm_num) _
            _ = (6 / 5 : ℝ) ^ (4 * selectedTrueCount s w) := (pow_mul _ _ _).symm
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) h
        rw [div_pow, one_pow, one_div, inv_mul_eq_div]
        exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
      · positivity
    _ = (3 / 4 : ℝ) ^ s.card * (6 / 5 : ℝ) ^ s.card := by
      rw [uniformAverage_mul_right, uniformAverage_selectedTrueHalfWeight]
    _ = _ := by rw [← mul_pow]; norm_num

lemma uniformProbability_selectedTrueCount_lower_tail_exp {ι : Type*} [Fintype ι]
    (s : Finset ι) :
    uniformProbability (fun w : ι → Bool ↦ 4 * selectedTrueCount s w ≤ s.card) ≤
      Real.exp (-(s.card : ℝ) / 16) := by
  refine (uniformProbability_selectedTrueCount_lower_tail s).trans ?_
  have hb : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 16)) := by
    have h := Real.add_one_le_exp (-(1 / 16 : ℝ))
    linarith
  calc
    _ ≤ Real.exp (-(1 / 16 : ℝ)) ^ s.card := pow_le_pow_left₀ (by norm_num) hb _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end OdlyzkoPoonen
