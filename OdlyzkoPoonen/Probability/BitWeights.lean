import OdlyzkoPoonen.Probability.UniformAverage
import OdlyzkoPoonen.Probability.TriangularBits

/-!
# Averaging bit weights

The generating polynomial for the number of true bits in a uniform Boolean word
is `(1+t)^n`. Normalization gives `((1+t)/2)^n`; at `t=1/2` this is the exact
factor `(3/4)^n`. Triangular bijections preserve this average.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

/-- Number of true coordinates in a Boolean word. -/
def trueBitCount {n : ℕ} (w : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i ↦ w i = true)).card

lemma pow_trueBitCount_eq_prod {n : ℕ} (w : Fin n → Bool) (t : ℝ) :
    t ^ trueBitCount w = ∏ i, if w i then t else 1 := by
  simp [trueBitCount, Finset.prod_ite]

lemma sum_pow_trueBitCount (n : ℕ) (t : ℝ) :
    (∑ w : Fin n → Bool, t ^ trueBitCount w) = (1 + t) ^ n := by
  have h := Finset.sum_prod_piFinset (ι := Fin n) (Finset.univ : Finset Bool)
    (fun _ b ↦ if b then t else 1)
  rw [Fintype.piFinset_univ] at h
  simpa [pow_trueBitCount_eq_prod, add_comm] using h

lemma uniformAverage_pow_trueBitCount (n : ℕ) (t : ℝ) :
    uniformAverage (fun w : Fin n → Bool ↦ t ^ trueBitCount w) =
      ((1 + t) / 2) ^ n := by
  rw [uniformAverage, sum_pow_trueBitCount]
  simp [div_pow]

lemma uniformAverage_half_pow_trueBitCount (n : ℕ) :
    uniformAverage (fun w : Fin n → Bool ↦ (1 / 2 : ℝ) ^ trueBitCount w) =
      (3 / 4 : ℝ) ^ n := by
  rw [uniformAverage_pow_trueBitCount]
  norm_num

lemma uniformAverage_triangular_half_weight {n : ℕ}
    {t : (Fin n → Bool) → Fin n → Bool} (ht : DependsOnEarlier t) :
    uniformAverage (fun w : Fin n → Bool ↦
      (1 / 2 : ℝ) ^ trueBitCount (triangularBitMap t w)) = (3 / 4 : ℝ) ^ n :=
  (uniformAverage_bijective (triangularBitMap_bijective ht)
    (fun w ↦ (1 / 2 : ℝ) ^ trueBitCount w)).trans
    (uniformAverage_half_pow_trueBitCount n)

end OdlyzkoPoonen
