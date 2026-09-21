import OdlyzkoPoonen.Asymptotics.SmallCyclotomicDeterminants
import OdlyzkoPoonen.Polynomial.CyclotomicProducts

/-!
# Leading terms for the six small cyclotomic events

The remainder improves by a full inverse power. The displayed coefficients
retain their exact determinant form for transparent finite arithmetic.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

lemma degreeProbability_cyclotomic_product_determinant_term
    (s : Finset ℕ) {q d : ℕ} {D : ℝ} (hq : 0 < q)
    (horders : ∀ k ∈ s, k ∣ q) (hone : 1 ∉ s)
    (hd : (cyclotomicProduct s).natDegree = d)
    (hD : (monicDivisorGramMatrix (cyclotomicProduct s) q).det = D) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ cyclotomicProduct s ∣ p) -
      (((2 * q : ℕ) : ℝ) / Real.pi) ^ ((d : ℝ) / 2) /
        Real.sqrt D * (n : ℝ) ^ (-(d : ℝ) / 2))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(d : ℝ) / 2 - 1)) := by
  have h := degreeProbability_monic_determinant_leading_term
    (cyclotomicProduct_monic s) hq (cyclotomicProduct_dvd_X_pow_sub_one hq horders)
    (cyclotomicProduct_dvd_geom_sum hq horders hone)
  simpa only [hd, hD] using h

lemma degreeProbability_cyclotomic_three_leading_term :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ cyclotomic 3 ℤ ∣ p) -
      (6 / Real.pi / Real.sqrt 3) * (n : ℝ) ^ (-1 : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) := by
  have hd : (cyclotomicProduct {3}).natDegree = 2 := by
    simp only [cyclotomicProduct, Finset.prod_singleton, natDegree_cyclotomic]
    decide
  have hD : (monicDivisorGramMatrix (cyclotomicProduct {3}) 3).det = 3 := by
    rw [show cyclotomicProduct {3} = cyclotomic 3 ℤ by simp [cyclotomicProduct]]
    exact cyclotomic_three_gram_determinant
  have h := degreeProbability_cyclotomic_product_determinant_term {3}
    (by decide : 0 < 3) (by simp) (by simp) hd hD
  norm_num [cyclotomicProduct] at h ⊢
  exact h

lemma degreeProbability_cyclotomic_four_leading_term :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ (cyclotomic 4 ℤ) ∣ p) -
      (8 / Real.pi / Real.sqrt 4) * (n : ℝ) ^ (-1 : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) := by
  have hd : (cyclotomicProduct {4}).natDegree = 2 := by
    simp only [cyclotomicProduct_natDegree, Finset.sum_singleton]
    decide
  have he : cyclotomicProduct {4} = cyclotomic 4 ℤ := by norm_num [cyclotomicProduct]
  have hD : (monicDivisorGramMatrix (cyclotomicProduct {4}) 4).det = 4 := by
    rw [he]
    exact cyclotomic_four_gram_determinant
  have h := degreeProbability_cyclotomic_product_determinant_term {4}
    (by decide : 0 < 4) (by simp) (by simp) hd hD
  rw [he] at h
  norm_num at h ⊢
  exact h

lemma degreeProbability_cyclotomic_six_leading_term :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ (cyclotomic 6 ℤ) ∣ p) -
      (12 / Real.pi / Real.sqrt 12) * (n : ℝ) ^ (-1 : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) := by
  have hd : (cyclotomicProduct {6}).natDegree = 2 := by
    simp only [cyclotomicProduct_natDegree, Finset.sum_singleton]
    decide
  have he : cyclotomicProduct {6} = cyclotomic 6 ℤ := by norm_num [cyclotomicProduct]
  have hD : (monicDivisorGramMatrix (cyclotomicProduct {6}) 6).det = 12 := by
    rw [he]
    exact cyclotomic_six_gram_determinant
  have h := degreeProbability_cyclotomic_product_determinant_term {6}
    (by decide : 0 < 6) (by simp) (by simp) hd hD
  rw [he] at h
  norm_num at h ⊢
  exact h

lemma degreeProbability_cyclotomic_two_three_leading_term :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ (cyclotomic 2 ℤ * cyclotomic 3 ℤ) ∣ p) -
      ((12 / Real.pi) ^ (3 / 2 : ℝ) / Real.sqrt 72) * (n : ℝ) ^ (-3 / 2 : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 2 : ℝ)) := by
  have hd : (cyclotomicProduct {2, 3}).natDegree = 3 := by
    rw [cyclotomicProduct_natDegree]
    norm_num [show Nat.totient 2 = 1 by decide, show Nat.totient 3 = 2 by decide]
  have he : cyclotomicProduct {2, 3} = cyclotomic 2 ℤ * cyclotomic 3 ℤ := by norm_num [cyclotomicProduct]
  have hD : (monicDivisorGramMatrix (cyclotomicProduct {2, 3}) 6).det = 72 := by
    rw [he]
    exact cyclotomic_two_three_gram_determinant
  have h := degreeProbability_cyclotomic_product_determinant_term {2, 3}
    (by decide : 0 < 6) (by simp) (by simp) hd hD
  rw [he] at h
  norm_num at h ⊢
  exact h

lemma degreeProbability_cyclotomic_two_four_leading_term :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ (cyclotomic 2 ℤ * cyclotomic 4 ℤ) ∣ p) -
      ((8 / Real.pi) ^ (3 / 2 : ℝ) / Real.sqrt 4) * (n : ℝ) ^ (-3 / 2 : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 2 : ℝ)) := by
  have hd : (cyclotomicProduct {2, 4}).natDegree = 3 := by
    rw [cyclotomicProduct_natDegree]
    norm_num [show Nat.totient 2 = 1 by decide, show Nat.totient 4 = 2 by decide]
  have he : cyclotomicProduct {2, 4} = cyclotomic 2 ℤ * cyclotomic 4 ℤ := by norm_num [cyclotomicProduct]
  have hD : (monicDivisorGramMatrix (cyclotomicProduct {2, 4}) 4).det = 4 := by
    rw [he]
    exact cyclotomic_two_four_gram_determinant
  have h := degreeProbability_cyclotomic_product_determinant_term {2, 4}
    (by decide : 0 < 4) (by simp) (by simp) hd hD
  rw [he] at h
  norm_num at h ⊢
  exact h

lemma degreeProbability_cyclotomic_two_six_leading_term :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ (cyclotomic 2 ℤ * cyclotomic 6 ℤ) ∣ p) -
      ((12 / Real.pi) ^ (3 / 2 : ℝ) / Real.sqrt 8) * (n : ℝ) ^ (-3 / 2 : ℝ))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 2 : ℝ)) := by
  have hd : (cyclotomicProduct {2, 6}).natDegree = 3 := by
    rw [cyclotomicProduct_natDegree]
    norm_num [show Nat.totient 2 = 1 by decide, show Nat.totient 6 = 2 by decide]
  have he : cyclotomicProduct {2, 6} = cyclotomic 2 ℤ * cyclotomic 6 ℤ := by norm_num [cyclotomicProduct]
  have hD : (monicDivisorGramMatrix (cyclotomicProduct {2, 6}) 6).det = 8 := by
    rw [he]
    exact cyclotomic_two_six_gram_determinant
  have h := degreeProbability_cyclotomic_product_determinant_term {2, 6}
    (by decide : 0 < 6) (by simp) (by simp) hd hD
  rw [he] at h
  norm_num at h ⊢
  exact h

end OdlyzkoPoonen
