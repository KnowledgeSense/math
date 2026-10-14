import SphericalTreeFailures.FiniteCharacteristicLimit
import SphericalTreeFailures.CensusCharacteristic
import SphericalTreeFailures.FiniteFourierEnvelope

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory

 theorem sizeExponential_scalar (a x t : ℝ) :
    sizeExponential (a * x) t = sizeExponential x (a * t) := by
  unfold sizeExponential
  apply congrArg Complex.exp
  push_cast
  ring

theorem sizeExponential_sub (x y t : ℝ) :
    sizeExponential (x - y) t = sizeExponential (-y) t * sizeExponential x t := by
  rw [← sizeExponential_add]
  congr 1
  ring

theorem normalizedSample_characteristic (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) :
    (∫ ω, sizeExponential (normalizedSample p k m activity i ω) t ∂totalSizeMeasure p k activity ha) =
      sizeExponential (-totalCenter p k m activity) (t / (-censusScale p) ^ m) *
        sampledCharacteristic p k m activity ha i (t / (-censusScale p) ^ m) := by
  unfold normalizedSample
  simp_rw [sizeExponential_scalar, sizeExponential_sub]
  rw [integral_const_mul]
  rw [show ((-censusScale p) ^ m)⁻¹ * t = t / (-censusScale p) ^ m by ring]
  rfl

theorem normalizedSample_characteristic_norm (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) :
    ‖∫ ω, sizeExponential (normalizedSample p k m activity i ω) t ∂totalSizeMeasure p k activity ha‖ =
      ‖sampledCharacteristic p k m activity ha i (t / (-censusScale p) ^ m)‖ := by
  rw [normalizedSample_characteristic, norm_mul, sizeExponential_norm, one_mul]

theorem scaledCensusLimit_characteristic (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) :
    (∫ ω, sizeExponential (scaledCensusLimit p k activity i ω) t ∂totalSizeMeasure p k activity ha) =
      censusCharacteristic p i ((tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * t) := by
  unfold scaledCensusLimit
  simp_rw [sizeExponential_scalar]
  have h := integral_fun_fst (μ := broadcastMeasure p) (ν := tailInputMeasure k activity ha)
    (fun ω => sizeExponential (censusLimit p i ω)
      ((tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * t))
  simp only [probReal_univ, one_smul] at h
  rw [show totalSizeMeasure p k activity ha = (broadcastMeasure p).prod
    (tailInputMeasure k activity ha) from rfl, h]
  exact (charFun_map_sizeExponential _ (measurable_censusLimit p i) _).symm

theorem sampledCharacteristic_norm_neg (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) :
    ‖sampledCharacteristic p k m activity ha i (-t)‖ =
      ‖sampledCharacteristic p k m activity ha i t‖ := by
  unfold sampledCharacteristic
  rw [← charFun_map_sizeExponential _ (measurable_sampledTotalSize k m i),
    ← charFun_map_sizeExponential _ (measurable_sampledTotalSize k m i), charFun_neg]
  exact Complex.norm_conj _

theorem sampledCharacteristic_signed_norm (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) :
    ‖sampledCharacteristic p k m activity ha i (t / (-censusScale p) ^ m)‖ =
      ‖sampledCharacteristic p k m activity ha i (t / censusScale p ^ m)‖ := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp
    (show (t / (-censusScale p) ^ m) ^ 2 = (t / censusScale p ^ m) ^ 2 by
      rw [div_pow, div_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm m 2, pow_mul, pow_mul, neg_sq]) with h | h
  · rw [h]
  · rw [h, sampledCharacteristic_norm_neg]

end SphericalTreeFailures
