import SphericalTreeFailures.HardCoreMoments
import Mathlib.Analysis.Complex.Exponential

namespace SphericalTreeFailures
open Polynomial

noncomputable def polynomialCharacteristic (p : ℕ[X]) (activity t : ℝ) : ℂ :=
  p.eval₂ (Nat.castRingHom ℂ) ((activity : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) /
    ((p.eval₂ (Nat.castRingHom ℝ) activity : ℝ) : ℂ)

theorem polynomialCharacteristic_mul (p q : ℕ[X]) (activity t : ℝ) :
    polynomialCharacteristic (p * q) activity t =
      polynomialCharacteristic p activity t * polynomialCharacteristic q activity t := by
  simp only [polynomialCharacteristic, eval₂_mul, Complex.ofReal_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem polynomialCharacteristic_pow (p : ℕ[X]) (activity t : ℝ) (n : ℕ) :
    polynomialCharacteristic (p ^ n) activity t = polynomialCharacteristic p activity t ^ n := by
  simp only [polynomialCharacteristic, eval₂_pow, Complex.ofReal_pow, div_pow]

theorem polynomialCharacteristic_X {activity : ℝ} (ha : 0 < activity) (t : ℝ) :
    polynomialCharacteristic X activity t = Complex.exp ((t : ℂ) * Complex.I) := by
  simp only [polynomialCharacteristic, eval₂_X]
  have h : (activity : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  field_simp

theorem polynomialCharacteristic_add_ratio (p q : ℕ[X]) {activity r : ℝ}
    (hr : 0 < r) (hp : 0 < p.eval₂ (Nat.castRingHom ℝ) activity)
    (hq : q.eval₂ (Nat.castRingHom ℝ) activity = r * p.eval₂ (Nat.castRingHom ℝ) activity)
    (t : ℝ) :
    polynomialCharacteristic (p + q) activity t =
      (1 / (1 + r) : ℝ) * polynomialCharacteristic p activity t +
      (r / (1 + r) : ℝ) * polynomialCharacteristic q activity t := by
  have hp' : ((p.eval₂ (Nat.castRingHom ℝ) activity : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hsum : (1 + (r : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + r : ℝ) ≠ 0 by positivity)
  simp only [polynomialCharacteristic, eval₂_add, hq, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one]
  have halg (A B a r : ℂ) (ha : a ≠ 0) (hr : r ≠ 0) (hs : 1 + r ≠ 0) :
      (A + B) / (a + r * a) = 1 / (1 + r) * (A / a) + r / (1 + r) * (B / (r * a)) := by
    have hd : a + r * a ≠ 0 := by
      have he : a + r * a = (1 + r) * a := by ring
      rw [he]
      exact mul_ne_zero hs ha
    field_simp
  exact halg _ _ _ _ hp' hr' hsum

end SphericalTreeFailures
