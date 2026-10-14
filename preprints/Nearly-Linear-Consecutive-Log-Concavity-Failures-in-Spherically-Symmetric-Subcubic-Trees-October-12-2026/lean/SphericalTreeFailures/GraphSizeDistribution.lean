import SphericalTreeFailures.TotalGraphLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory

noncomputable def graphSizeLaw (m k : ℕ) (activity : ℝ) (ha : 0 < activity) : Measure ℝ :=
  (hardCore (sphericalTree m (2 * k + 1)).graph activity ha).toMeasure.map
    (fun s => (s.val.card : ℝ))

instance (m k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    IsProbabilityMeasure (graphSizeLaw m k activity ha) := by
  unfold graphSizeLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).mpr inferInstance

theorem charFun_map_sizeExponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} (hf : Measurable f) (t : ℝ) :
    charFun (μ.map f) t = ∫ ω, sizeExponential (f ω) t ∂μ := by
  rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => by
    unfold sizeExponential
    apply congrArg Complex.exp
    ring

theorem rootSelectedSize_has_graphLaw (p : unitInterval) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hp : (p : ℝ) = broadcastParameter r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (m : ℕ) :
    HasLaw (rootSelectedSize k m) (graphSizeLaw m k (tunedActivity r) (tunedActivity_pos hr))
      (totalSizeMeasure p k (tunedActivity r) (tunedActivity_pos hr)) := by
  refine ⟨(measurable_rootSelectedSize k m).aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_map_sizeExponential _ (measurable_rootSelectedSize k m),
    rootSelected_characteristic_graph p k hr hp htune]
  unfold graphSizeLaw
  rw [charFun_map_sizeExponential _ (measurable_of_finite _)]
  have h := hardCore_characteristic (sphericalTree m (2 * k + 1)).graph
    (tunedActivity r) (tunedActivity_pos hr) t
  simpa only [sizeExponential, Complex.ofReal_natCast] using h.symm

end SphericalTreeFailures
