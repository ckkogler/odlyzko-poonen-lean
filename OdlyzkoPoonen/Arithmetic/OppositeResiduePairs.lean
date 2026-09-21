import OdlyzkoPoonen.Arithmetic.ResidueClassSize
import OdlyzkoPoonen.Probability.OppositeIndices
import Mathlib.Data.Nat.ModEq

/-!
# Opposite coefficient positions in one residue class

For an odd modulus there is a residue whose double is the total degree.
The lower positions in this residue have their opposite positions in the same
residue. Counting complete blocks gives a uniform lower bound for their number.
-/

namespace OdlyzkoPoonen
open scoped Classical

lemma exists_half_residue {q : ℕ} (hq : Odd q) (n : ℕ) :
    ∃ a : ℕ, a < q ∧ (2 * a) % q = n % q := by
  have hq0 : 0 < q := hq.pos
  have he : 2 * ((q + 1) / 2) = q + 1 := by
    obtain ⟨k, hk⟩ := hq
    omega
  refine ⟨(n * ((q + 1) / 2)) % q, Nat.mod_lt _ hq0, ?_⟩
  calc
    _ = (2 * (n * ((q + 1) / 2))) % q := by simp [Nat.mul_mod]
    _ = (n * (2 * ((q + 1) / 2))) % q := by congr 1; ring
    _ = n % q := by rw [he]; simp [Nat.mul_add]

noncomputable def oppositeResiduePairs (m q a : ℕ) : Finset (Fin (m / 2)) :=
  Finset.univ.filter (fun j ↦ (j.val + 1) % q = a)

lemma oppositeResiduePairs_positions {m q a : ℕ} (ha : a < q)
    (hdouble : (2 * a) % q = (m + 1) % q)
    (j : Fin (m / 2)) (hj : j ∈ oppositeResiduePairs m q a) :
    ((lowerWordIndex j).val + 1) % q = a ∧
      ((upperWordIndex j).val + 1) % q = a := by
  have hl : (j.val + 1) % q = a := (Finset.mem_filter.mp hj).2
  refine ⟨hl, ?_⟩
  have hlo : j.val + 1 ≡ a [MOD q] := by
    change (j.val + 1) % q = a % q
    rwa [Nat.mod_eq_of_lt ha]
  have he : (upperWordIndex j).val + 1 + (j.val + 1) = m + 1 := by
    rw [upperWordIndex_val]
    have := j.isLt
    omega
  have hsum : (upperWordIndex j).val + 1 + (j.val + 1) ≡ a + a [MOD q] := by
    rw [he, ← two_mul]
    exact hdouble.symm
  have h := hlo.add_right_cancel hsum
  change ((upperWordIndex j).val + 1) % q = a % q at h
  simpa only [Nat.mod_eq_of_lt ha] using h

lemma oppositeResiduePairs_card_ge (m : ℕ) {q a : ℕ} (hq : 0 < q) (ha : a < q) :
    (m / 2) / q ≤ (oppositeResiduePairs m q a).card := by
  have h := card_positive_residue_class_ge (m / 2) hq ⟨a, ha⟩
  simpa only [Fintype.card_subtype, oppositeResiduePairs] using h

lemma oppositeResiduePairs_card_add_one_ge (m : ℕ) {q a : ℕ}
    (hq : 0 < q) (ha : a < q) :
    ((m / 2 : ℕ) + 1 : ℝ) / q ≤ (oppositeResiduePairs m q a).card + 1 := by
  have h := card_positive_residue_class_add_one_ge (m / 2) hq ⟨a, ha⟩
  simpa only [Fintype.card_subtype, oppositeResiduePairs] using h

lemma oppositeResiduePairs_card_ge_degree {n q a : ℕ}
    (hq : 0 < q) (ha : a < q) (hn : 4 * q ≤ n) :
    (n : ℝ) / (4 * q) ≤ (oppositeResiduePairs (n - 1) q a).card := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf : q ≤ (n - 1) / 2 := by omega
  have hcard := oppositeResiduePairs_card_ge (n - 1) hq ha
  have hc1 : (1 : ℝ) ≤ (oppositeResiduePairs (n - 1) q a).card := by
    exact_mod_cast (Nat.div_pos hhalf hq).trans_le hcard
  have hadd := (div_le_iff₀ hqR).mp
    (oppositeResiduePairs_card_add_one_ge (n - 1) hq ha)
  have hhalfR : (n : ℝ) ≤ 2 * (((n - 1) / 2 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show n ≤ 2 * ((n - 1) / 2 + 1) by omega)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * q)).mpr
  nlinarith

end OdlyzkoPoonen
