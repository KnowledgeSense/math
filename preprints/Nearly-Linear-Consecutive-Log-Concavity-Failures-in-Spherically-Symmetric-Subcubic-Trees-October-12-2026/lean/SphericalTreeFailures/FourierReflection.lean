import SphericalTreeFailures.LocalLimitTheorem

namespace SphericalTreeFailures
open MeasureTheory
set_option maxRecDepth 2048

theorem complexFourierIntegral_reflection (φ : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    complexFourierIntegral (fun t => φ (-t)) n x =
      (-1 : ℂ) ^ n * complexFourierIntegral φ n (-x) := by
  unfold complexFourierIntegral
  have h (t : ℝ) : (-(t : ℂ) * Complex.I) ^ n * inverseFourierKernel t (x : ℂ) * φ (-t) =
      (-1 : ℂ) ^ n * ((-((-t : ℝ) : ℂ) * Complex.I) ^ n *
        inverseFourierKernel (-t) ((-x : ℝ) : ℂ) * φ (-t)) := by
    have he : inverseFourierKernel t (x : ℂ) = inverseFourierKernel (-t) ((-x : ℝ) : ℂ) := by
      unfold inverseFourierKernel
      congr 1
      push_cast
      ring
    rw [he]
    push_cast
    simp only [neg_neg]
    rw [show -(t : ℂ) * Complex.I = (-1 : ℂ) * ((t : ℂ) * Complex.I) by ring, mul_pow]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  have hi := integral_neg_eq_self (fun t : ℝ => (-(t : ℂ) * Complex.I) ^ n * inverseFourierKernel t ((-x : ℝ) : ℂ) * φ t)
  rw [hi]
  push_cast
  ring

theorem realFourierIntegral_reflection (φ : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    realFourierIntegral (fun t => φ (-t)) n x =
      (-1 : ℝ) ^ n * realFourierIntegral φ n (-x) := by
  unfold realFourierIntegral
  rw [complexFourierIntegral_reflection]
  have he : (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.ofReal_neg]

theorem parityFourierIntegral (k : ℕ) (hk : 16384 ≤ k) (m n : ℕ) (x : ℝ) :
    realFourierIntegral (parityCharacteristic k hk m) n x =
      ((-1 : ℝ) ^ m) ^ n * realFourierIntegral (releaseCharacteristic k hk) n ((-1 : ℝ) ^ m * x) := by
  unfold parityCharacteristic
  rcases neg_one_pow_eq_or (R := ℝ) m with h | h
  · simp [h]
  · simp only [h, neg_one_mul]
    exact realFourierIntegral_reflection _ _ _

end SphericalTreeFailures
