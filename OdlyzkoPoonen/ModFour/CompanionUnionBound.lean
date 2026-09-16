import OdlyzkoPoonen.ModFour.FactorWitnesses

/-!
# Summing the degree-split witness bounds

Every actual companion has a factor witness with smaller degree between one
and half the original degree. A finite union over those splits and the exact
witness-space normalization give the first companion probability bound.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma HasModFourCompanion.exists_factor_witness {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hcomp : HasModFourCompanion n p) :
    ∃ i : Fin (n / 2), HasFactorWitness (i.val + 1) (n - (i.val + 1)) p := by
  obtain ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hpab, hna, hcong⟩ := hcomp.factorization hp
  let i : Fin (n / 2) := ⟨d - 1, by omega⟩
  have hi : i.val + 1 = d := by dsimp [i]; omega
  have he : n - (i.val + 1) = e := by omega
  refine ⟨i, ?_⟩
  rw [hi, show n - d = e by omega]
  exact ⟨a, b, ha, hb, hpab, hna, hcong⟩

lemma binaryProbability_companion_le_split_sum (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
      ∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2) := by
  unfold binaryProbability
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ i : Fin (n / 2), HasFactorWitness (i.val + 1) (n - (i.val + 1)) (wordPolynomial w)) := by
      apply uniformProbability_mono
      intro w hw
      have hp : HasBinaryEndpoints n (wordPolynomial w) := by
        simpa only [Nat.sub_add_cancel hn] using wordPolynomial_endpoints w
      exact hw.exists_factor_witness hp
    _ ≤ ∑ i : Fin (n / 2), uniformProbability (fun w : Fin (n - 1) → Bool ↦
        HasFactorWitness (i.val + 1) (n - (i.val + 1)) (wordPolynomial w)) :=
      uniformProbability_exists_le_sum
        (fun (i : Fin (n / 2)) (w : Fin (n - 1) → Bool) ↦
          HasFactorWitness (i.val + 1) (n - (i.val + 1)) (wordPolynomial w))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := i.isLt
      have hd : 1 ≤ i.val + 1 := by omega
      have hde : i.val + 1 ≤ n - (i.val + 1) := by omega
      have hsum : i.val + 1 + (n - (i.val + 1)) = n := by omega
      have hbound := binaryProbability_factor_witness_le hd hde
      rw [hsum] at hbound
      exact hbound

end OdlyzkoPoonen
