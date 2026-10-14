import MainTheorems.Hypercomb.RealSequences
import Mathlib.Algebra.Polynomial.Coeff

namespace ResearchMain.Hypercomb

open Polynomial

def coefficientSequence (p : ℝ[X]) (k : ℤ) : ℝ := if 0 ≤ k then p.coeff k.toNat else 0

theorem coefficientSequence_add (p q : ℝ[X]) (k : ℤ) :
    coefficientSequence (p + q) k = coefficientSequence p k + coefficientSequence q k := by
  by_cases hk : 0 ≤ k <;> simp [coefficientSequence, hk]

theorem coefficientSequence_C_mul (b : ℝ) (p : ℝ[X]) (k : ℤ) :
    coefficientSequence (C b * p) k = b * coefficientSequence p k := by
  by_cases hk : 0 ≤ k <;> simp [coefficientSequence, hk]

theorem coefficientSequence_mul_X (p : ℝ[X]) (k : ℤ) :
    coefficientSequence (p * X) k = coefficientSequence p (k - 1) := by
  by_cases hk : k < 0
  · rw [coefficientSequence, ite_eq_right (by omega), coefficientSequence, ite_eq_right (by omega)]
  · by_cases hk0 : k = 0
    · subst k
      simp [coefficientSequence]
    · have hkpos : 0 ≤ k := by omega
      have hkprev : 0 ≤ k - 1 := by omega
      have hknat : k.toNat = (k - 1).toNat + 1 := by omega
      simp only [coefficientSequence, ite_eq_left hkpos, ite_eq_left hkprev, hknat, coeff_mul_X]

theorem coefficientSequence_trinomial (p : ℝ[X]) (b c : ℝ) (k : ℤ) :
    coefficientSequence (p * (1 + C b * X + C c * X ^ 2)) k =
      tripleSum (coefficientSequence p) b c k := by
  have hid : p * (1 + C b * X + C c * X ^ 2) =
      p + C b * (p * X) + C c * ((p * X) * X) := by ring
  rw [hid, coefficientSequence_add, coefficientSequence_add,
    coefficientSequence_C_mul, coefficientSequence_C_mul, coefficientSequence_mul_X,
    coefficientSequence_mul_X, coefficientSequence_mul_X]
  rw [show k - 1 - 1 = k - 2 by omega]
  rfl

theorem coefficientSequence_one (k : ℤ) :
    coefficientSequence (1 : ℝ[X]) k = if k = 0 then 1 else 0 := by
  by_cases hk : 0 ≤ k
  · simp only [coefficientSequence, ite_eq_left hk, coeff_one]
    have he : k.toNat = 0 ↔ k = 0 := by omega
    simp only [he]
  · have hk0 : k ≠ 0 := by omega
    simp [coefficientSequence, hk, hk0]

theorem coefficientSequence_one_positiveLC : PositiveLC (coefficientSequence 1) 0 := by
  constructor
  · intro k hk0 hke
    have he : k = 0 := by omega
    simp [he, coefficientSequence_one]
  · intro k hk
    rw [coefficientSequence_one, ite_eq_right (by omega)]
  · intro k
    by_cases hkm : k - 1 = 0
    · have hkp : k + 1 ≠ 0 := by omega
      simp only [coefficientSequence_one, ite_eq_right hkp, mul_zero]
      positivity
    · simp only [coefficientSequence_one, ite_eq_right hkm, zero_mul]
      positivity

theorem PositiveLC.coefficients_linear {p : ℝ[X]} {e : ℕ}
    (hp : PositiveLC (coefficientSequence p) e) {b : ℝ} (hb : 0 < b) :
    PositiveLC (coefficientSequence (p * (1 + C b * X))) (e + 1) := by
  have heq : coefficientSequence (p * (1 + C b * X)) = tripleSum (coefficientSequence p) b 0 := by
    funext k
    simpa only [map_zero, zero_mul, add_zero] using coefficientSequence_trinomial p b 0 k
  rw [heq]
  exact hp.linear hb

theorem PositiveLC.coefficients_quadratic {p : ℝ[X]} {e : ℕ}
    (hp : PositiveLC (coefficientSequence p) e) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbc : c ≤ b ^ 2) :
    PositiveLC (coefficientSequence (p * (1 + C b * X + C c * X ^ 2))) (e + 2) := by
  have heq : coefficientSequence (p * (1 + C b * X + C c * X ^ 2)) =
      tripleSum (coefficientSequence p) b c := funext (coefficientSequence_trinomial p b c)
  rw [heq]
  exact hp.quadratic hb hc hbc

end ResearchMain.Hypercomb
