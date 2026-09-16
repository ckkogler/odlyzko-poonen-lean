import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# Products over repeated finite families

Indexing a root family by a group, a copy number and a root makes its pair
multiplicities explicit. Each pair of groups contributes its root-pair product
raised to the product of the two copy counts.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma prod_repeated_pairs {ι M : Type*} [Fintype ι] [CommMonoid M]
    {β : ι → Type*} [∀ t, Fintype (β t)] (w : ι → ℕ)
    (F : ∀ t, β t → ∀ u, β u → M) :
    (∏ i : (Σ t, Fin (w t) × β t), ∏ j : (Σ t, Fin (w t) × β t),
      F i.1 i.2.2 j.1 j.2.2) =
      ∏ t, ∏ u, (∏ a, ∏ b, F t a u b) ^ (w t * w u) := by
  simp only [Fintype.prod_sigma, Fintype.prod_prod_type, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  apply Finset.prod_congr rfl
  intro t ht
  rw [Finset.prod_comm, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro u hu
  rw [Finset.prod_pow, ← pow_mul, Nat.mul_comm]

end OdlyzkoPoonen
