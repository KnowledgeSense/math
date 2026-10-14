import SphericalTreeFailures.FiniteCharacteristicLimit

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable def normalizedRootSample (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ω : TotalSizeSpace k) : ℝ :=
  ((-censusScale p) ^ m)⁻¹ * (rootSelectedSize k m ω - totalCenter p k m activity)

noncomputable def scaledRootLimit (p : unitInterval) (k : ℕ) (activity : ℝ)
    (ω : TotalSizeSpace k) : ℝ :=
  (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * rootMixtureLimit p ω.1

theorem measurable_normalizedRootSample (p : unitInterval) (k m : ℕ) (activity : ℝ) :
    Measurable (normalizedRootSample p k m activity) :=
  measurable_const.mul ((measurable_rootSelectedSize k m).sub measurable_const)

theorem measurable_scaledRootLimit (p : unitInterval) (k : ℕ) (activity : ℝ) :
    Measurable (scaledRootLimit p k activity) :=
  measurable_const.mul ((measurable_rootMixtureLimit p).comp measurable_fst)

theorem memLp_rootTotalError (p : unitInterval) (hp : 0 < (p : ℝ)) (k m : ℕ)
    (activity : ℝ) (ha : 0 < activity) :
    MemLp (rootTotalError p k m activity) 2 (totalSizeMeasure p k activity ha) := by
  apply (rootTotalError_bound p k m activity ha).trans_lt
  exact ENNReal.add_lt_top.mpr ⟨(memLp_sample_error p hp k m activity ha false).eLpNorm_lt_top,
    (memLp_sample_error p hp k m activity ha true).eLpNorm_lt_top⟩

noncomputable def rootErrorNorm (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) : ℝ :=
  (eLpNorm (rootTotalError p k m activity) 2 (totalSizeMeasure p k activity ha)).toReal

theorem rootErrorNorm_tendsto (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    Tendsto (fun m => rootErrorNorm p k m activity ha) atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (rootSelectedSize_tendsto_L2 p hc k activity ha)

theorem root_characteristic_error_bound (p : unitInterval) (hp : 0 < (p : ℝ))
    (k m : ℕ) (activity : ℝ) (ha : 0 < activity) (t : ℝ) :
    ‖(∫ ω, sizeExponential (normalizedRootSample p k m activity ω) t ∂totalSizeMeasure p k activity ha) -
      ∫ ω, sizeExponential (scaledRootLimit p k activity ω) t ∂totalSizeMeasure p k activity ha‖ ≤
        |t| * rootErrorNorm p k m activity ha :=
  characteristic_difference_L2_bound _ (measurable_normalizedRootSample p k m activity)
    (measurable_scaledRootLimit p k activity) (memLp_rootTotalError p hp k m activity ha) t

end SphericalTreeFailures
