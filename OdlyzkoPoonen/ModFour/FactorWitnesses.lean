import OdlyzkoPoonen.ModFour.CompanionReduction
import OdlyzkoPoonen.ModFour.FactorProbability
import OdlyzkoPoonen.Probability.ImageBound
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# Counting factor witnesses for a fixed degree split

A factor witness need not be unique. Injectivity of the original polynomial's
word representation and the image-cardinality bound therefore give an upper
bound using all qualifying independent factor pairs. The ratio of the two
finite space sizes is exactly one half, cancelling the factor two in the
factor-pair probability estimate.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- A qualifying factor-pair witness of the specified degrees for an integer polynomial. -/
def HasFactorWitness (d e : ℕ) (p : ℤ[X]) : Prop :=
  ∃ a b : (ZMod 2)[X], HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
    p = zeroOneLift (a * b) ∧ a ≠ a.reverse ∧
    CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
      (autocorrelation (zeroOneLift (a * b.reverse)))

lemma hasFactorWitness_iff_words {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (p : ℤ[X]) :
    HasFactorWitness d e p ↔
      ∃ v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool),
        (f2WordPolynomial v.1 ≠ (f2WordPolynomial v.1).reverse ∧
          CongruentMod 4
            (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2)))
            (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * (f2WordPolynomial v.2).reverse)))) ∧
        p = zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2) := by
  constructor
  · rintro ⟨a, b, ha, hb, hp, hna, hcong⟩
    have ha' : HasF2Endpoints ((d - 1) + 1) a := by simpa only [Nat.sub_add_cancel hd] using ha
    have hb' : HasF2Endpoints ((e - 1) + 1) b := by simpa only [Nat.sub_add_cancel he] using hb
    obtain ⟨u, rfl⟩ := exists_f2WordPolynomial_eq ha'
    obtain ⟨v, rfl⟩ := exists_f2WordPolynomial_eq hb'
    exact ⟨⟨u, v⟩, ⟨hna, hcong⟩, hp⟩
  · rintro ⟨⟨u, v⟩, ⟨hna, hcong⟩, hp⟩
    refine ⟨f2WordPolynomial u, f2WordPolynomial v, ?_, ?_, hp, hna, hcong⟩
    · simpa only [Nat.sub_add_cancel hd] using f2WordPolynomial_endpoints u
    · simpa only [Nat.sub_add_cancel he] using f2WordPolynomial_endpoints v

lemma factor_pair_word_card_ratio {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (Fintype.card ((Fin (d - 1) → Bool) × (Fin (e - 1) → Bool)) : ℝ) /
      Fintype.card (Fin (d + e - 1) → Bool) = (1 / 2 : ℝ) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_add, show d + e - 1 = (d - 1 + (e - 1)) + 1 by omega, pow_succ]
  field_simp

lemma binaryProbability_factor_witness_le {d e : ℕ} (hd : 1 ≤ d) (hde : d ≤ e) :
    binaryProbability (d + e - 1) (HasFactorWitness d e) ≤
      (3 / 4 : ℝ) ^ ((e - 1) / 2) := by
  have he : 1 ≤ e := hd.trans hde
  let E (v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool)) : Prop :=
    f2WordPolynomial v.1 ≠ (f2WordPolynomial v.1).reverse ∧
      CongruentMod 4
        (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2)))
        (autocorrelation (zeroOneLift (f2WordPolynomial v.1 * (f2WordPolynomial v.2).reverse)))
  have hbound := uniformProbability_exists_image_le
    (fun v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool) ↦
      zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2))
    (@wordPolynomial (d + e - 1)) wordPolynomial_injective E
  rw [factor_pair_word_card_ratio hd he] at hbound
  have hevent : binaryProbability (d + e - 1) (HasFactorWitness d e) =
      uniformProbability (fun w : Fin (d + e - 1) → Bool ↦
        ∃ v : (Fin (d - 1) → Bool) × (Fin (e - 1) → Bool),
          E v ∧ wordPolynomial w = zeroOneLift (f2WordPolynomial v.1 * f2WordPolynomial v.2)) := by
    unfold binaryProbability
    congr 1
    funext w
    exact propext (hasFactorWitness_iff_words hd he (wordPolynomial w))
  have hpair : uniformProbability E ≤ 2 * (3 / 4 : ℝ) ^ ((e - 1) / 2) :=
    factor_pair_congruence_probability d e hd hde
  rw [hevent]
  calc
    _ ≤ uniformProbability E * (1 / 2 : ℝ) := hbound
    _ ≤ (2 * (3 / 4 : ℝ) ^ ((e - 1) / 2)) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hpair (by norm_num)
    _ = _ := by ring

end OdlyzkoPoonen
