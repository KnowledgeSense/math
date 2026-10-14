import SphericalTreeFailures.TotalBranchIndependence
import SphericalTreeFailures.HardCoreCharacteristic
import SphericalTreeFailures.CharacteristicRecursion
import SphericalTreeFailures.CharacteristicBounds

set_option backward.isDefEq.respectTransparency false

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset

noncomputable def sizeExponential (x t : ℝ) : ℂ := Complex.exp ((x : ℂ) * ((t : ℂ) * Complex.I))

theorem sizeExponential_add (x y t : ℝ) :
    sizeExponential (x + y) t = sizeExponential x t * sizeExponential y t := by
  simp only [sizeExponential, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem measurable_sizeExponential (t : ℝ) : Measurable (fun x => sizeExponential x t) := by
  unfold sizeExponential
  fun_prop

theorem sizeExponential_norm (x t : ℝ) : ‖sizeExponential x t‖ = 1 := by
  unfold sizeExponential
  simp [Complex.norm_exp]

theorem integrable_sizeExponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (t : ℝ) :
    Integrable (fun ω => sizeExponential (f ω) t) μ := by
  apply Integrable.of_bound ((measurable_sizeExponential t).comp hf).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => le_of_eq (sizeExponential_norm _ _)

noncomputable def sampledCharacteristic (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) : ℂ :=
  ∫ ω, sizeExponential (sampledTotalSize k m i ω) t ∂totalSizeMeasure p k activity ha

theorem tailSample_characteristic (k : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) (t : ℝ) :
    (∫ s, sizeExponential (selectedTailSize k i s) t ∂tailSampleMeasure k activity ha) =
      polynomialCharacteristic (pathPolynomial (if i then 2 * k else 2 * k + 1)) activity t := by
  cases i
  · have h := integral_fun_fst
      (μ := (hardCore (pendantPath (2 * k + 1)).graph activity ha).toMeasure)
      (ν := (hardCore (pendantPath (2 * k)).graph activity ha).toMeasure)
      (fun s : IndependentConfiguration (pendantPath (2 * k + 1)).graph =>
        Complex.exp ((s.val.card : ℂ) * ((t : ℂ) * Complex.I)))
    simp only [probReal_univ, one_smul] at h
    rw [hardCore_characteristic, pathPolynomial_graph] at h
    simpa only [tailSampleMeasure, selectedTailSize, Bool.false_eq_true, ite_false, sizeExponential,
      Complex.ofReal_natCast] using h
  · have h := integral_fun_snd
      (μ := (hardCore (pendantPath (2 * k + 1)).graph activity ha).toMeasure)
      (ν := (hardCore (pendantPath (2 * k)).graph activity ha).toMeasure)
      (fun s : IndependentConfiguration (pendantPath (2 * k)).graph =>
        Complex.exp ((s.val.card : ℂ) * ((t : ℂ) * Complex.I)))
    simp only [probReal_univ, one_smul] at h
    rw [hardCore_characteristic, pathPolynomial_graph] at h
    simpa only [tailSampleMeasure, selectedTailSize, ite_true, sizeExponential, Complex.ofReal_natCast] using h

theorem sampledCharacteristic_zero (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) (t : ℝ) :
    sampledCharacteristic p k 0 activity ha i t =
      if i then presentCharacteristic 0 k activity t else absentCharacteristic 0 k activity t := by
  unfold sampledCharacteristic
  simp_rw [sampledTotalSize_zero, sizeExponential_add]
  rw [integral_const_mul]
  have h := integral_fun_snd (μ := broadcastMeasure p) (ν := tailInputMeasure k activity ha)
    (fun τ => sizeExponential (selectedTailSize k i (τ [])) t)
  simp only [probReal_univ, one_smul] at h
  rw [show totalSizeMeasure p k activity ha = (broadcastMeasure p).prod
    (tailInputMeasure k activity ha) from rfl, h]
  have he := (tail_input_law k activity ha []).integral_comp
    (measurable_of_finite (fun s => sizeExponential (selectedTailSize k i s) t)).aestronglyMeasurable
  change (∫ τ, sizeExponential (selectedTailSize k i (τ [])) t ∂tailInputMeasure k activity ha) = _ at he
  rw [he, tailSample_characteristic]
  cases i <;> simp [boolIndicator, sizeExponential, absentCharacteristic, presentCharacteristic,
    conditionalPolynomials, polynomialCharacteristic_mul, polynomialCharacteristic_X ha]

end SphericalTreeFailures
