import OdlyzkoPoonen.LinearAlgebra.ConfluentIntegerLowerBound
import OdlyzkoPoonen.Polynomial.RootPowerFamilies

/-!
# Prime lower bound for the root-power confluent determinant

The original roots occur `k` times, and each distinct prime-power family occurs
once. Primes which separate the original roots make each family simple. The
noncyclotomic conjugate-power theorem separates different families. Integer
resultants then yield `(product primes)^(2*degree*k)` as a lower bound for the
squared determinant norm. The finite family and its ordering are explicit.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma root_power_determinant_lower_bound {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (α : Fin J.natDegree → ℂ) (hα : Function.Injective α)
    (hmem : ∀ j, α j ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hfac : J.map (Int.castRingHom ℂ) = ∏ j, (X - C (α j)))
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    (k : ℕ) {n : ℕ}
    (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree)) :
    (∏ i, (p i : ℝ)) ^ (2 * J.natDegree * k) ≤
      ‖(confluentVandermonde (fun i ↦
        α (e i).2.2 ^ ((e i).1.elim 1 p))).det‖ ^ 2 := by
  let r (t : Option ι) := t.elim 1 p
  let f (t : Option ι) := polynomialRootPowers J (r t)
  let x (t : Option ι) (a : Fin J.natDegree) := α a ^ r t
  have hr : Function.Injective r := by
    intro t u he
    cases t with
    | none =>
      cases u with
      | none => rfl
      | some i => exact False.elim ((hp i).ne_one he.symm)
    | some i =>
      cases u with
      | none => exact False.elim ((hp i).ne_one he)
      | some j => exact congrArg some (hpinj he)
  have hf (t : Option ι) : (f t).map (Int.castRingHom ℂ) =
      ∏ a, (X - C (x t a)) := root_power_family_factorization α hfac (r t)
  have hx (t : Option ι) : Function.Injective (x t) := by
    cases t with
    | none => simpa only [x, r, Option.elim_none, pow_one] using hα
    | some i => exact root_power_family_injective α hα hmem (hsep i)
  have hcop (t u : Option ι) (htu : t ≠ u) :
      IsCoprime ((f t).map (Int.castRingHom ℂ)) ((f u).map (Int.castRingHom ℂ)) := by
    simp only [f, polynomialRootPowers_map _
      (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)]
    exact rootPowers_isCoprime_of_distinct_exponents hJ hirr hconst hcyc
      (fun he ↦ htu (hr he))
  have hdet := norm_det_confluent_ge_cross_product k f x hf hx hcop e
  have hpbound (i : ι) : (p i : ℝ) ^ J.natDegree ≤
      ‖resultant ((f (some i)).map (Int.castRingHom ℂ))
        ((f none).map (Int.castRingHom ℂ))‖ := by
    change (p i : ℝ) ^ J.natDegree ≤
      ‖resultant ((polynomialRootPowers J (p i)).map (Int.castRingHom ℂ))
        ((polynomialRootPowers J 1).map (Int.castRingHom ℂ))‖
    rw [polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ)
      from Int.cast_injective), polynomialRootPowers_map _
      (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
      polynomialRootPowers_one_complex (hJ.map _)]
    exact prime_pow_degree_le_norm_rootPower_resultant hJ hirr hconst hcyc (hp i)
  have hprod : (∏ i, (p i : ℝ) ^ J.natDegree) ≤
      ∏ i, ‖resultant ((f (some i)).map (Int.castRingHom ℂ))
        ((f none).map (Int.castRingHom ℂ))‖ :=
    Finset.prod_le_prod (fun i _ ↦ by positivity) (fun i _ ↦ hpbound i)
  have hpow := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ ↦ by positivity)) hprod (2 * k)
  rw [Finset.prod_pow, ← pow_mul] at hpow
  have he : J.natDegree * (2 * k) = 2 * J.natDegree * k := by ring
  rw [he] at hpow
  exact hpow.trans hdet

end OdlyzkoPoonen
