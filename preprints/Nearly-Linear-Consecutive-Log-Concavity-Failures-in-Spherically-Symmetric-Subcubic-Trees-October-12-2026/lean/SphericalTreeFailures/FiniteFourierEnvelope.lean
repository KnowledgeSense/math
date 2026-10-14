import SphericalTreeFailures.LatticeBound
import Mathlib.Topology.Algebra.Polynomial

namespace SphericalTreeFailures

noncomputable def rawEnvelope (m k : ℕ) (r t : ℝ) : ℝ :=
  max ‖absentCharacteristic m k (tunedActivity r) t‖ ‖presentCharacteristic m k (tunedActivity r) t‖
noncomputable def scaledEnvelope (m k : ℕ) (r t : ℝ) : ℝ :=
  rawEnvelope m k r (t / fluctuationScale r ^ m)

theorem rawEnvelope_nonneg (m k : ℕ) (r t : ℝ) : 0 ≤ rawEnvelope m k r t :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem tuned_totalCharacteristic_norm_le (k : ℕ) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) (t : ℝ) :
    ‖totalCharacteristic m k (tunedActivity r) t‖ ≤ rawEnvelope m k r t := by
  have hp0 : 0 ≤ broadcastParameter r := by unfold broadcastParameter; positivity
  have hp1 : broadcastParameter r ≤ 1 := by
    unfold broadcastParameter
    apply (div_le_one (by positivity : 0 < 1 + r)).mpr
    linarith
  have he0 : 0 ≤ 1 - broadcastParameter r := by linarith
  rw [tuned_characteristic_mixture k hr htune]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0, abs_of_nonneg hp0]
  have h0 := mul_le_mul_of_nonneg_left (le_max_left
    ‖absentCharacteristic m k (tunedActivity r) t‖ ‖presentCharacteristic m k (tunedActivity r) t‖) he0
  have h1 := mul_le_mul_of_nonneg_left (le_max_right
    ‖absentCharacteristic m k (tunedActivity r) t‖ ‖presentCharacteristic m k (tunedActivity r) t‖) hp0
  unfold rawEnvelope
  nlinarith

theorem rawEnvelope_succ (k : ℕ) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) (t : ℝ) :
    rawEnvelope (m + 1) k r t ≤ rawEnvelope m k r t ^ 2 := by
  unfold rawEnvelope
  apply max_le
  · rw [absentCharacteristic_succ, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (tuned_totalCharacteristic_norm_le k hr htune m t) 2
  · rw [presentCharacteristic_succ m k (tunedActivity_pos hr), norm_mul,
      unit_exponential_norm, one_mul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2

theorem scaledEnvelope_succ (k : ℕ) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) (t : ℝ) :
    scaledEnvelope (m + 1) k r t ≤ scaledEnvelope m k r (t / fluctuationScale r) ^ 2 := by
  have hg : fluctuationScale r ≠ 0 := by unfold fluctuationScale broadcastParameter; positivity
  have he : t / fluctuationScale r ^ (m + 1) = (t / fluctuationScale r) / fluctuationScale r ^ m := by
    rw [pow_succ]
    field_simp
  unfold scaledEnvelope
  rw [he]
  exact rawEnvelope_succ k hr htune m _

theorem polynomialCharacteristic_continuous (p : Polynomial ℕ) (activity : ℝ) :
    Continuous (polynomialCharacteristic p activity) := by
  have he : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  exact ((p.continuous_eval₂ (Nat.castRingHom ℂ)).comp (continuous_const.mul he)).div_const _

theorem rawEnvelope_continuous (m k : ℕ) (r : ℝ) : Continuous (rawEnvelope m k r) :=
  ((polynomialCharacteristic_continuous _ _).norm).max ((polynomialCharacteristic_continuous _ _).norm)

theorem scaledEnvelope_continuous (m k : ℕ) (r : ℝ) : Continuous (scaledEnvelope m k r) :=
  (rawEnvelope_continuous m k r).comp (continuous_id.div_const _)

end SphericalTreeFailures
