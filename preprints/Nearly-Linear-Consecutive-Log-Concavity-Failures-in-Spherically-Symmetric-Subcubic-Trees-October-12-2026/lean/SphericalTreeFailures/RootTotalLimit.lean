import SphericalTreeFailures.TotalLimit
import SphericalTreeFailures.TotalMixture

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable def rootTotalError (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ω : TotalSizeSpace k) : ℝ :=
  ((-censusScale p) ^ m)⁻¹ * (rootSelectedSize k m ω - totalCenter p k m activity) -
    (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * rootMixtureLimit p ω.1

theorem rootTotalError_bound (p : unitInterval) (k m : ℕ) (activity : ℝ) (ha : 0 < activity) :
    eLpNorm (rootTotalError p k m activity) 2 (totalSizeMeasure p k activity ha) ≤
      eLpNorm (fun ω : TotalSizeSpace k =>
        ((-censusScale p) ^ m)⁻¹ * (sampledTotalSize k m false ω - totalCenter p k m activity) -
          (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * censusLimit p false ω.1)
        2 (totalSizeMeasure p k activity ha) +
      eLpNorm (fun ω : TotalSizeSpace k =>
        ((-censusScale p) ^ m)⁻¹ * (sampledTotalSize k m true ω - totalCenter p k m activity) -
          (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * censusLimit p true ω.1)
        2 (totalSizeMeasure p k activity ha) := by
  let s : Set (TotalSizeSpace k) := {ω | ω.1 [] = true}
  have hm : Measurable (fun ω : TotalSizeSpace k => ω.1 []) :=
    (measurable_pi_apply []).comp measurable_fst
  have hs : MeasurableSet s := hm (measurableSet_singleton true)
  let err := fun i (ω : TotalSizeSpace k) =>
    ((-censusScale p) ^ m)⁻¹ * (sampledTotalSize k m i ω - totalCenter p k m activity) -
      (tailMeanDifference k activity + censusScale p / (1 + censusScale p)) * censusLimit p i ω.1
  have he : rootTotalError p k m activity = sᶜ.indicator (err false) + s.indicator (err true) := by
    funext ω
    cases hh : ω.1 [] <;> simp [rootTotalError, rootSelectedSize, rootMixtureLimit, s, err, hh]
  rw [he]
  exact (eLpNorm_add_le (by norm_num)).trans
    (add_le_add (eLpNorm_indicator_le _ hs.compl) (eLpNorm_indicator_le _ hs))

theorem rootSelectedSize_tendsto_L2 (p : unitInterval) (hc : 1 < 2 * (p : ℝ) ^ 2)
    (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    Tendsto (fun m => eLpNorm (rootTotalError p k m activity) 2 (totalSizeMeasure p k activity ha))
      atTop (𝓝 0) := by
  have ht := (sampledTotalSize_tendsto_L2 p hc k activity ha false).add
    (sampledTotalSize_tendsto_L2 p hc k activity ha true)
  simp only [zero_add] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun m => rootTotalError_bound p k m activity ha)

end SphericalTreeFailures
