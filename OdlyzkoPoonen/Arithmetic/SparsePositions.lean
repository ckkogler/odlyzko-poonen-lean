import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Counting the internal positions divisible by a spacing

An internal bit indexed by `i : Fin m` is the coefficient of `X^(i+1)`.
Consequently the number of selected positive multiples of `q` is exactly
`m / q`, with natural division. The count includes spacing zero and empty words.
-/

namespace OdlyzkoPoonen

lemma card_sparse_internal_positions (m q : ℕ) :
    Nat.card {i : Fin m // q ∣ i.val + 1} = m / q := by
  rw [Nat.card_eq_fintype_card]
  let s : Finset ℕ := (Finset.range m).filter (fun k ↦ q ∣ k + 1)
  let e : {i : Fin m // q ∣ i.val + 1} ≃ s :=
    { toFun := fun i ↦ ⟨i.val.val, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr i.val.isLt, i.property⟩⟩
      invFun := fun k ↦ ⟨⟨k.val, Finset.mem_range.mp (Finset.mem_filter.mp k.property).1⟩,
        (Finset.mem_filter.mp k.property).2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    _ = Fintype.card s :=
      Fintype.card_congr e
    _ = m / q := by simpa only [Fintype.card_coe] using Nat.card_multiples m q

end OdlyzkoPoonen
