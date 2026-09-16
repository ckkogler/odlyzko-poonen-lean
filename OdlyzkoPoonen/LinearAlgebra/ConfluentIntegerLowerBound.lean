import OdlyzkoPoonen.LinearAlgebra.ConfluentResultants
import OdlyzkoPoonen.LinearAlgebra.SymmetricProductBounds
import OdlyzkoPoonen.Polynomial.IntegerRootProducts

/-!
# An integer lower bound for a confluent determinant

Repeat the roots of one distinguished integer polynomial `k` times and the
roots of each other polynomial once. Assuming the simple root families have
pairwise coprime polynomials, all derivative and cross-resultants have norm at
least one. Keeping the distinguished row and column yields the product of its
cross-resultants to the power `2*k`.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma norm_resultant_comm (f g : ℂ[X]) : ‖resultant f g‖ = ‖resultant g f‖ := by
  rw [resultant_comm]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

lemma norm_det_confluent_ge_cross_product {ι : Type*} [Fintype ι]
    {β : Option ι → Type*} [∀ t, Fintype (β t)] (k : ℕ)
    (J : Option ι → ℤ[X]) (x : ∀ t, β t → ℂ)
    (hf : ∀ t, (J t).map (Int.castRingHom ℂ) = ∏ a, (X - C (x t a)))
    (hx : ∀ t, Function.Injective (x t))
    (hcop : ∀ t u, t ≠ u → IsCoprime ((J t).map (Int.castRingHom ℂ))
      ((J u).map (Int.castRingHom ℂ)))
    {n : ℕ} (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × β t)) :
    (∏ i : ι, ‖resultant ((J (some i)).map (Int.castRingHom ℂ))
      ((J none).map (Int.castRingHom ℂ))‖) ^ (2 * k) ≤
      ‖(confluentVandermonde (fun i ↦ x (e i).1 (e i).2.2)).det‖ ^ 2 := by
  let f (t : Option ι) := (J t).map (Int.castRingHom ℂ)
  let w (t : Option ι) := t.elim k (fun _ ↦ 1)
  let A (t u : Option ι) : ℝ :=
    (if t = u then ‖resultant (f t) (f t).derivative‖
      else ‖resultant (f t) (f u)‖) ^ (w t * w u)
  have hA (t u : Option ι) : 1 ≤ A t u := by
    apply one_le_pow₀
    by_cases htu : t = u
    · subst u
      rw [ite_eq_left rfl]
      exact one_le_norm_derivative_resultant_of_integer_root_family (J t) (x t) (hx t) (hf t)
    · rw [ite_eq_right htu]
      exact one_le_norm_resultant_int (hcop t u htu)
  have hsym (t u : Option ι) : A t u = A u t := by
    by_cases htu : t = u
    · subst u; rfl
    · simp only [A, ite_eq_right htu, ite_eq_right (Ne.symm htu)]
      rw [norm_resultant_comm, Nat.mul_comm]
  have h := option_symmetric_prod_lower A hA hsym
    (fun i ↦ ‖resultant (f (some i)) (f none)‖ ^ k)
    (fun i ↦ pow_nonneg (norm_nonneg _) _)
    (fun i ↦ by simp [A, w])
  have he := norm_det_confluent_eq_resultant_product w x f hf hx
    (fun t u htu a b ↦ root_families_disjoint_of_isCoprime
      (x t) (x u) (hf t) (hf u) (hcop t u htu) a b) e
  rw [he]
  simpa only [Finset.prod_pow, ← pow_mul, Nat.mul_comm k 2, A, f] using h

end OdlyzkoPoonen
