import SphericalTreeFailures.TailModel
import Mathlib.Probability.Independence.Integration

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable def tailSampleNoise (k : ℕ) (activity : ℝ) (i : Bool) (s : TailSamples k) : ℝ :=
  selectedTailSize k i s - selectedTailMean k activity i

theorem selectedTailMean_bounds (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    0 ≤ selectedTailMean k activity i ∧ selectedTailMean k activity i ≤ 2 * (k : ℝ) + 1 := by
  rw [← integral_selectedTailSize k activity ha i]
  constructor
  · exact integral_nonneg (selectedTailSize_nonneg k i)
  · have h := integral_mono (μ := tailSampleMeasure k activity ha)
      (f := selectedTailSize k i) (g := fun _ => 2 * (k : ℝ) + 1)
      Integrable.of_finite (integrable_const _) (selectedTailSize_le k i)
    simpa using h

theorem tailSampleNoise_integral (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    ∫ s, tailSampleNoise k activity i s ∂tailSampleMeasure k activity ha = 0 := by
  unfold tailSampleNoise
  rw [integral_sub Integrable.of_finite (integrable_const _), integral_selectedTailSize]
  simp

theorem tailSampleNoise_abs_le (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) (s : TailSamples k) :
    |tailSampleNoise k activity i s| ≤ 2 * (k : ℝ) + 1 := by
  obtain ⟨hm0, hm⟩ := selectedTailMean_bounds k activity ha i
  have hs0 := selectedTailSize_nonneg k i s
  have hs := selectedTailSize_le k i s
  unfold tailSampleNoise
  rw [abs_le]
  constructor <;> linarith

theorem tailSampleNoise_sq_integral_le (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    ∫ s, tailSampleNoise k activity i s ^ 2 ∂tailSampleMeasure k activity ha ≤ (2 * (k : ℝ) + 1) ^ 2 := by
  have h := integral_mono (μ := tailSampleMeasure k activity ha)
    (f := fun s => tailSampleNoise k activity i s ^ 2) (g := fun _ => (2 * (k : ℝ) + 1) ^ 2)
    Integrable.of_finite (integrable_const _) (fun s => by
      have hb := tailSampleNoise_abs_le k activity ha i s
      have hs := sq_le_sq₀ (abs_nonneg (tailSampleNoise k activity i s)) (by positivity : 0 ≤ 2 * (k : ℝ) + 1)
      simpa only [sq_abs] using hs.mpr hb)
  simpa using h

noncomputable def tailNoise (k m : ℕ) (activity : ℝ) (i : Bool) (ω : TotalSizeSpace k) : ℝ :=
  ∑ v ∈ binaryLevel m, tailSampleNoise k activity (broadcastState i ω.1 v) (ω.2 v)

theorem tail_input_law (k : ℕ) (activity : ℝ) (ha : 0 < activity) (v : BinaryNode) :
    HasLaw (fun τ : TailInputSpace k => τ v) (tailSampleMeasure k activity ha)
      (tailInputMeasure k activity ha) := by
  exact ⟨(measurable_pi_apply v).aemeasurable, Measure.infinitePi_map_eval _ v⟩

theorem tail_inputs_independent (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    iIndepFun (fun v (τ : TailInputSpace k) => τ v) (tailInputMeasure k activity ha) :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

end SphericalTreeFailures
