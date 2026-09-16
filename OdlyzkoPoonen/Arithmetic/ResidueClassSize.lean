import Mathlib.Tactic

/-!
# Free coefficients in a residue class

Internal coefficient positions are numbered `i+1` for `i : Fin m`. Every
residue class modulo a positive `k` contains at least `m/k` such positions.
An explicit injection takes one position in each complete block of length `k`.
-/

namespace OdlyzkoPoonen
open scoped Classical

lemma card_positive_residue_class_ge (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) :
    m / k ≤ Fintype.card {i : Fin m // (i.val + 1) % k = r.val} := by
  let a := if r.val = 0 then k - 1 else r.val - 1
  have ha : a < k := by dsimp [a]; split_ifs <;> have := r.isLt <;> omega
  have har : (a + 1) % k = r.val := by
    dsimp [a]
    split_ifs with hr
    · rw [Nat.sub_add_cancel hk, Nat.mod_self, hr]
    · rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt r.isLt]
  let e : Fin (m / k) → {i : Fin m // (i.val + 1) % k = r.val} := fun j ↦
    ⟨⟨a + k * j.val, by
        have h₁ := Nat.mul_le_mul_left k (show j.val + 1 ≤ m / k by omega)
        have h₂ := Nat.mul_div_le m k
        nlinarith⟩, by
      change (a + k * j.val + 1) % k = r.val
      calc
        _ = ((a + 1) + k * j.val) % k := by congr 1; omega
        _ = (a + 1) % k := by simp
        _ = _ := har⟩
  have he : Function.Injective e := by
    intro i j hij
    have h := congrArg (fun x ↦ x.val.val) hij
    dsimp [e] at h
    apply Fin.ext
    nlinarith
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he

lemma card_positive_residue_class_add_one_ge (m : ℕ) {k : ℕ}
    (hk : 0 < k) (r : Fin k) :
    (m + 1 : ℝ) / k ≤
      (Fintype.card {i : Fin m // (i.val + 1) % k = r.val} : ℝ) + 1 := by
  have hc := card_positive_residue_class_ge m hk r
  have hd : m + 1 ≤ k * (m / k + 1) := by
    have := Nat.mod_lt m hk
    have := Nat.mod_add_div m k
    nlinarith
  have hm : m + 1 ≤ k * (Fintype.card {i : Fin m // (i.val + 1) % k = r.val} + 1) :=
    hd.trans (Nat.mul_le_mul_left k (by omega))
  apply (div_le_iff₀ (by exact_mod_cast hk)).mpr
  exact_mod_cast (by simpa only [mul_comm] using hm)

end OdlyzkoPoonen
