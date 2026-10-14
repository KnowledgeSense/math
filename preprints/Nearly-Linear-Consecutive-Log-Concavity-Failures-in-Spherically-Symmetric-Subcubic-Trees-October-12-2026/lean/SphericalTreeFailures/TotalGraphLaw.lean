import SphericalTreeFailures.TotalMixture

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory

 theorem subtree_characteristic_square (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ha : 0 < activity) {f : TotalSizeSpace k → ℝ} (hf : Measurable f) (t : ℝ) :
    (∫ ω, sizeExponential (f (totalSubtree k false ω)) t *
      sizeExponential (f (totalSubtree k true ω)) t ∂totalSizeMeasure p k activity ha) =
        (∫ ω, sizeExponential (f ω) t ∂totalSizeMeasure p k activity ha) ^ 2 := by
  have hF := (measurable_sizeExponential t).comp hf
  have hi := (totalSubtree_independent p k activity ha).comp hF hF
  have h := hi.integral_fun_mul_eq_mul_integral
    (hF.comp (measurable_totalSubtree k false)).aestronglyMeasurable
    (hF.comp (measurable_totalSubtree k true)).aestronglyMeasurable
  have h0 := (totalSubtree_preserving p k activity ha false).hasLaw.integral_comp hF.aestronglyMeasurable
  have h1 := (totalSubtree_preserving p k activity ha true).hasLaw.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_apply] at h h0 h1
  rw [h0, h1] at h
  simpa only [pow_two] using h

theorem sampledCharacteristic_succ_true (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (t : ℝ) :
    sampledCharacteristic p k (m + 1) activity ha true t =
      Complex.exp ((t : ℂ) * Complex.I) * sampledCharacteristic p k m activity ha false t ^ 2 := by
  unfold sampledCharacteristic
  simp_rw [sampledTotalSize_succ]
  simp only [broadcastState, boolIndicator, ite_true]
  simp_rw [sizeExponential_add]
  simp_rw [mul_assoc]
  rw [integral_const_mul, subtree_characteristic_square p k activity ha (measurable_sampledTotalSize k m false)]
  simp [sizeExponential]

theorem sampledCharacteristic_succ_false (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (t : ℝ) :
    sampledCharacteristic p k (m + 1) activity ha false t =
      (((1 - (p : ℝ) : ℝ) : ℂ) * sampledCharacteristic p k m activity ha false t +
        (p : ℂ) * sampledCharacteristic p k m activity ha true t) ^ 2 := by
  unfold sampledCharacteristic
  simp_rw [sampledTotalSize_succ]
  simp only [broadcastState, boolIndicator, Bool.false_eq_true, ite_false, zero_add]
  have he (b : Bool) (ω : TotalSizeSpace k) :
      sampledTotalSize k m (ω.1 [b]) (totalSubtree k b ω) = rootSelectedSize k m (totalSubtree k b ω) := rfl
  simp_rw [he, sizeExponential_add]
  rw [subtree_characteristic_square p k activity ha (measurable_rootSelectedSize k m),
    rootSelected_characteristic]
  rfl

theorem sampledCharacteristic_graph (p : unitInterval) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hp : (p : ℝ) = broadcastParameter r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) (t : ℝ) :
    sampledCharacteristic p k m (tunedActivity r) (tunedActivity_pos hr) false t =
      absentCharacteristic m k (tunedActivity r) t ∧
    sampledCharacteristic p k m (tunedActivity r) (tunedActivity_pos hr) true t =
      presentCharacteristic m k (tunedActivity r) t := by
  induction m with
  | zero => simp [sampledCharacteristic_zero]
  | succ m ih =>
    rw [sampledCharacteristic_succ_false, sampledCharacteristic_succ_true, ih.1, ih.2,
      absentCharacteristic_succ, presentCharacteristic_succ _ _ (tunedActivity_pos hr),
      tuned_characteristic_mixture k hr htune, hp]
    exact ⟨rfl, rfl⟩

theorem rootSelected_characteristic_graph (p : unitInterval) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hp : (p : ℝ) = broadcastParameter r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) (t : ℝ) :
    (∫ ω, sizeExponential (rootSelectedSize k m ω) t
      ∂totalSizeMeasure p k (tunedActivity r) (tunedActivity_pos hr)) =
      polynomialCharacteristic
        (independencePolynomial (sphericalTree m (2 * k + 1)).graph Finset.univ) (tunedActivity r) t := by
  rw [rootSelected_characteristic]
  obtain ⟨h0, h1⟩ := sampledCharacteristic_graph p k hr hp htune m t
  rw [h0, h1, hp, ← tuned_characteristic_mixture k hr htune]
  exact totalCharacteristic_graph m k (tunedActivity r) t

end SphericalTreeFailures
