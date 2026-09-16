import OdlyzkoPoonen.Probability.BinomialAtoms

/-!
# Fair-bit sums on arbitrary finite index sets

Reindexing by an equivalence with `Fin` transfers the binomial atom estimate to
an arbitrary finite block. The bound depends only on the number of free bits;
fixed endpoint contributions are permitted as an arbitrary integer shift.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

lemma uniformProbability_finite_bit_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a z : ℤ) :
    uniformProbability (fun w : ι → Bool ↦ a + ∑ i, bitValue (w i) = z) ≤
      4 / Real.sqrt ((Fintype.card ι : ℝ) + 1) := by
  let e := Fintype.equivFin ι
  let ew : (Fin (Fintype.card ι) → Bool) ≃ (ι → Bool) :=
    { toFun := fun w i ↦ w (e i)
      invFun := fun w i ↦ w (e.symm i)
      left_inv := fun w ↦ by funext i; simp
      right_inv := fun w ↦ by funext i; simp }
  calc
    _ = uniformProbability
        (fun w : Fin (Fintype.card ι) → Bool ↦ a + ∑ i : ι, bitValue (w (e i)) = z) :=
      (uniformProbability_equiv ew (fun w : ι → Bool ↦ a + ∑ i, bitValue (w i) = z)).symm
    _ = uniformProbability
        (fun w : Fin (Fintype.card ι) → Bool ↦ a + ∑ i, bitValue (w i) = z) := by
      congr 1
      funext w
      rw [e.sum_comp (fun i ↦ bitValue (w i))]
    _ ≤ _ := uniformProbability_shifted_bitValue_sum_le _ a z

end OdlyzkoPoonen
