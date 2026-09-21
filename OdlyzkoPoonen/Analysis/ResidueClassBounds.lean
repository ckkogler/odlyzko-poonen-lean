import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic

/-!
# Gluing estimates over finitely many residue classes

A fixed finite family of asymptotic bounds has a common constant and threshold.
Consequently bounds proved on all progressions give a bound on the full sequence.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped BigOperators

theorem isBigO_of_residue_classes {f g : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (h : ∀ r : Fin q, (fun k ↦ f (q * k + r.val)) =O[atTop]
      (fun k ↦ g (q * k + r.val))) : f =O[atTop] g := by
  choose C hC using fun r ↦ isBigO_iff.mp (h r)
  have hall : ∀ᶠ k in atTop, ∀ r : Fin q,
      ‖f (q * k + r.val)‖ ≤ C r * ‖g (q * k + r.val)‖ :=
    Filter.eventually_all.mpr hC
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  apply isBigO_iff.mpr
  refine ⟨∑ r : Fin q, |C r|, ?_⟩
  filter_upwards [eventually_ge_atTop (q * N)] with n hn
  let r : Fin q := ⟨n % q, Nat.mod_lt n hq⟩
  have hquot : N ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hn)
  have he := hN (n / q) hquot r
  have hdecomp : q * (n / q) + r.val = n := Nat.div_add_mod n q
  rw [hdecomp] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (le_abs_self (C r)).trans (Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i))
    (Finset.mem_univ r))

end OdlyzkoPoonen
