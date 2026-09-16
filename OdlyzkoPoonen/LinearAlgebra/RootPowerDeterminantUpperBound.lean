import OdlyzkoPoonen.LinearAlgebra.ConfluentVandermondeBound
import OdlyzkoPoonen.LinearAlgebra.RepeatedRootCounts
import OdlyzkoPoonen.Analysis.RepeatedRootMahler
import OdlyzkoPoonen.Polynomial.RootPowerFamilyInjectivity

/-!
# Mahler upper bound for the root-power determinant

For `s` distinct good primes, the repeated family has `N=d*(k+s)` nodes. Its
norm product is exactly `M(J)^(k+sum primes)`. Counting each occurrence order
by its group's multiplicity gives a coarse but uniform determinant bound.
No sharp Hadamard or discriminant inequality is required.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma root_power_determinant_upper_bound {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (α : Fin J.natDegree → ℂ) (hα : Function.Injective α)
    (hmem : ∀ j, α j ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hfac : J.map (Int.castRingHom ℂ) = ∏ j, (X - C (α j)))
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    (k : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree)) :
    ‖(confluentVandermonde (fun i ↦ α (e i).2.2 ^ ((e i).1.elim 1 p))).det‖ ≤
      (n : ℝ) ^ (J.natDegree * (k ^ 2 + k + 2 * Fintype.card ι)) *
        (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ (n * (k + ∑ i, p i)) := by
  let w (t : Option ι) := t.elim k (fun _ ↦ 1)
  let r (t : Option ι) := t.elim 1 p
  let x (t : Option ι) (a : Fin J.natDegree) := α a ^ r t
  have hx : Function.Injective (fun z : Option ι × Fin J.natDegree ↦ x z.1 z.2) := by
    apply root_power_pair_injective hJ hirr hconst hcyc r
      (option_prime_exponents_injective p hpinj hp) α hα hmem
    intro t
    cases t with
    | none => simp [r]
    | some i => exact hsep i
  have hdim : n = J.natDegree * (k + Fintype.card ι) := by
    have h := (Fintype.card_congr e).trans (card_repeated_option_family k)
    simpa only [Fintype.card_fin] using h
  have hcount : (∑ i, rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i) ≤
      J.natDegree * (k ^ 2 + Fintype.card ι) := by
    simpa only [w, Fintype.card_fin, Fintype.sum_option, Option.elim_none,
      Option.elim_some, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Nat.cast_id] using sum_rootPrefixMultiplicity_repeated_le w x hx e
  have hexp : n + (∑ i, rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i) ≤
      J.natDegree * (k ^ 2 + k + 2 * Fintype.card ι) := by
    calc
      _ ≤ n + J.natDegree * (k ^ 2 + Fintype.card ι) := Nat.add_le_add_left hcount n
      _ = _ := by rw [hdim]; ring
  have hupper := norm_det_confluentVandermonde_le_power
    (fun i ↦ α (e i).2.2 ^ (e i).1.elim 1 p)
  rw [prod_max_norm_option_root_powers k p α hfac e, ← pow_mul,
    Nat.mul_comm (k + ∑ i, p i) n] at hupper
  exact hupper.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by exact_mod_cast hn) hexp)
    (pow_nonneg (mahlerMeasure_nonneg _) _))

end OdlyzkoPoonen
