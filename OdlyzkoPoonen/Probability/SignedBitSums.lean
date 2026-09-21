import OdlyzkoPoonen.Probability.FiniteBitSums

/-!
# Exact laws for signed sums of fair bits

Complementing the bits with negative sign converts a signed sum into an
ordinary binomial sum plus a deterministic integer shift. The index set may
be any finite block, so the result applies directly to residue partitions.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

def signedBitComplement {ι : Type*} (positive : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun w i := if positive i then w i else !(w i)
  invFun w i := if positive i then w i else !(w i)
  left_inv w := by funext i; cases h : positive i <;> simp [h]
  right_inv w := by funext i; cases h : positive i <;> simp [h]

def negativeSignCount {ι : Type*} [Fintype ι] (positive : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun i ↦ positive i = false)).card

def signedBitSum {ι : Type*} [Fintype ι] (positive : ι → Bool) (w : ι → Bool) : ℤ :=
  ∑ i, if positive i then bitValue (w i) else -bitValue (w i)

lemma negativeSignCount_eq_sum {ι : Type*} [Fintype ι] (positive : ι → Bool) :
    (negativeSignCount positive : ℤ) = ∑ i, if positive i then (0 : ℤ) else 1 := by
  simp only [negativeSignCount, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases positive i <;> simp

lemma signedBitSum_eq_complemented_sum {ι : Type*} [Fintype ι]
    (positive : ι → Bool) (w : ι → Bool) :
    signedBitSum positive w =
      (∑ i, bitValue (signedBitComplement positive w i)) - negativeSignCount positive := by
  rw [negativeSignCount_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases hs : positive i <;> cases hw : w i <;>
    simp [signedBitComplement, bitValue, hs, hw]

lemma uniformProbability_finite_bit_sum_eq {ι : Type*} [Fintype ι]
    (t : ℕ) :
    uniformProbability (fun w : ι → Bool ↦ (∑ i, bitValue (w i)) = (t : ℤ)) =
      ((Fintype.card ι).choose t : ℝ) / (2 : ℝ) ^ Fintype.card ι := by
  let e := Fintype.equivFin ι
  let ew : (Fin (Fintype.card ι) → Bool) ≃ (ι → Bool) :=
    { toFun := fun w i ↦ w (e i)
      invFun := fun w i ↦ w (e.symm i)
      left_inv := fun w ↦ by funext i; simp
      right_inv := fun w ↦ by funext i; simp }
  calc
    _ = uniformProbability
        (fun w : Fin (Fintype.card ι) → Bool ↦ (∑ i : ι, bitValue (w (e i))) = (t : ℤ)) :=
      (uniformProbability_equiv ew (fun w : ι → Bool ↦ (∑ i, bitValue (w i)) = (t : ℤ))).symm
    _ = uniformProbability (fun w : Fin (Fintype.card ι) → Bool ↦ trueBitCount w = t) := by
      congr 1
      funext w
      rw [e.sum_comp (fun i ↦ bitValue (w i)), sum_bitValue_eq_trueBitCount]
      simp
    _ = _ := uniformProbability_trueBitCount _ _

theorem uniformProbability_signedBitSum {ι : Type*} [Fintype ι]
    (positive : ι → Bool) (t : ℕ) :
    uniformProbability (fun w : ι → Bool ↦
      signedBitSum positive w = (t : ℤ) - negativeSignCount positive) =
      ((Fintype.card ι).choose t : ℝ) / (2 : ℝ) ^ Fintype.card ι := by
  have he : (fun w : ι → Bool ↦ signedBitSum positive w =
      (t : ℤ) - negativeSignCount positive) =
      (fun w ↦ (∑ i, bitValue (signedBitComplement positive w i)) = (t : ℤ)) := by
    funext w
    apply propext
    rw [signedBitSum_eq_complemented_sum]
    omega
  rw [he]
  rw [uniformProbability_equiv (signedBitComplement positive)
    (fun w : ι → Bool ↦ (∑ i, bitValue (w i)) = (t : ℤ))]
  exact uniformProbability_finite_bit_sum_eq t

end OdlyzkoPoonen
