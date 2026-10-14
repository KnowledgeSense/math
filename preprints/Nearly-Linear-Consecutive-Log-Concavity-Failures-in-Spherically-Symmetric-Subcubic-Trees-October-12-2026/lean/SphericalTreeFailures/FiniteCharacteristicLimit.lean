import SphericalTreeFailures.CharacteristicConvergence

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable def normalizedSample (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (i : Bool) (ω : TotalSizeSpace k) : ℝ :=
  ((-censusScale p) ^ m)⁻¹ * (sampledTotalSize k m i ω - totalCenter p k m activity)

noncomputable def scaledCensusLimit (p : unitInterval) (k : ℕ) (activity : ℝ)
    (i : Bool) (ω : TotalSizeSpace k) : ℝ :=
  (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * censusLimit p i ω.1

theorem measurable_normalizedSample (p : unitInterval) (k m : ℕ) (activity : ℝ) (i : Bool) :
    Measurable (normalizedSample p k m activity i) :=
  measurable_const.mul ((measurable_sampledTotalSize k m i).sub measurable_const)

theorem measurable_scaledCensusLimit (p : unitInterval) (k : ℕ) (activity : ℝ) (i : Bool) :
    Measurable (scaledCensusLimit p k activity i) :=
  measurable_const.mul ((measurable_censusLimit p i).comp measurable_fst)

theorem memLp_sample_error (p : unitInterval) (hp : 0 < (p : ℝ)) (k m : ℕ)
    (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    MemLp (normalizedSample p k m activity i - scaledCensusLimit p k activity i) 2
      (totalSizeMeasure p k activity ha) := by
  have h := (Lp.memLp (totalFluctuationL2 p k m activity ha i)).sub
    (Lp.memLp (totalLimitL2 p k activity ha i))
  exact h.ae_eq ((totalFluctuationL2_ae_eq p hp k m activity ha i).sub
    (totalLimitL2_ae_eq p k activity ha i))

noncomputable def sampleErrorNorm (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) : ℝ :=
  (eLpNorm (normalizedSample p k m activity i - scaledCensusLimit p k activity i) 2
    (totalSizeMeasure p k activity ha)).toReal

theorem sampleErrorNorm_tendsto (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    Tendsto (fun m => sampleErrorNorm p k m activity ha i) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (sampledTotalSize_tendsto_L2 p hc k activity ha i)
  exact h

theorem finite_characteristic_error_bound (p : unitInterval) (hp : 0 < (p : ℝ))
    (k m : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) (t : ℝ) :
    ‖(∫ ω, sizeExponential (normalizedSample p k m activity i ω) t ∂totalSizeMeasure p k activity ha) -
      ∫ ω, sizeExponential (scaledCensusLimit p k activity i ω) t ∂totalSizeMeasure p k activity ha‖ ≤
        |t| * sampleErrorNorm p k m activity ha i :=
  characteristic_difference_L2_bound _ (measurable_normalizedSample p k m activity i)
    (measurable_scaledCensusLimit p k activity i) (memLp_sample_error p hp k m activity ha i) t

theorem finite_characteristic_uniform_on_bounded (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) (R : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ t : ℝ, |t| ≤ R →
      ‖(∫ ω, sizeExponential (normalizedSample p k m activity i ω) t ∂totalSizeMeasure p k activity ha) -
        ∫ ω, sizeExponential (scaledCensusLimit p k activity i ω) t ∂totalSizeMeasure p k activity ha‖ < ε := by
  have hp : 0 < (p : ℝ) := by nlinarith [p.property.1]
  have ht := (sampleErrorNorm_tendsto p hc k activity ha i).const_mul R
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with m hm
  intro t htR
  exact (finite_characteristic_error_bound p hp k m activity ha i t).trans_lt
    ((mul_le_mul_of_nonneg_right htR ENNReal.toReal_nonneg).trans_lt hm)

end SphericalTreeFailures
