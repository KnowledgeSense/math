import SphericalTreeFailures.PolynomialCharacteristic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace SphericalTreeFailures
open Polynomial Finset

theorem unit_exponential_norm (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp]

theorem polynomialCharacteristic_norm_le_one (p : ℕ[X]) {activity : ℝ}
    (ha : 0 < activity) (hp : 0 < p.eval₂ (Nat.castRingHom ℝ) activity) (t : ℝ) :
    ‖polynomialCharacteristic p activity t‖ ≤ 1 := by
  unfold polynomialCharacteristic
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  apply (div_le_one hp).mpr
  rw [eval₂_eq_sum, sum_def, eval₂_eq_sum, sum_def]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  simp only [norm_mul, norm_pow, unit_exponential_norm, mul_one]
  change ‖((p.coeff j : ℕ) : ℂ)‖ * ‖(activity : ℂ)‖ ^ j ≤ _
  simp [Complex.norm_real, abs_of_pos ha]

theorem positive_unit_pair_norm_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne : u ≠ v) :
    ‖(a : ℂ) * u + (b : ℂ) * v‖ < a + b := by
  have hua : ‖(a : ℂ) * u‖ = a := by simp [hu, abs_of_pos ha]
  have hvb : ‖(b : ℂ) * v‖ = b := by simp [hv, abs_of_pos hb]
  have hle := norm_add_le ((a : ℂ) * u) ((b : ℂ) * v)
  rw [hua, hvb] at hle
  apply lt_of_le_of_ne hle
  intro heq
  have heq' : ‖(a : ℂ) * u + (b : ℂ) * v‖ = ‖(a : ℂ) * u‖ + ‖(b : ℂ) * v‖ := by
    rw [hua, hvb]
    exact heq
  have hc := norm_add_eq_iff_real.mp heq'
  rw [hua, hvb] at hc
  simp only [Complex.real_smul] at hc
  have hab : (b : ℂ) * (a : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast (ne_of_gt hb)) (by exact_mod_cast (ne_of_gt ha))
  apply hne
  apply mul_left_cancel₀ hab
  calc
    (b : ℂ) * (a : ℂ) * u = (b : ℂ) * ((a : ℂ) * u) := by ring
    _ = (a : ℂ) * ((b : ℂ) * v) := hc
    _ = (b : ℂ) * (a : ℂ) * v := by ring

end SphericalTreeFailures
