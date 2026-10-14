import SphericalTreeFailures.Broadcast
import SphericalTreeFailures.HardCoreMoments
import SphericalTreeFailures.TunedConstants
import Mathlib.MeasureTheory.Integral.Prod

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset

abbrev TailSamples (k : ℕ) :=
  IndependentConfiguration (pendantPath (2 * k + 1)).graph ×
    IndependentConfiguration (pendantPath (2 * k)).graph

noncomputable def tailSampleMeasure (k : ℕ) (activity : ℝ) (ha : 0 < activity) : Measure (TailSamples k) :=
  (hardCore (pendantPath (2 * k + 1)).graph activity ha).toMeasure.prod
    (hardCore (pendantPath (2 * k)).graph activity ha).toMeasure

instance (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    IsProbabilityMeasure (tailSampleMeasure k activity ha) := by
  unfold tailSampleMeasure
  infer_instance

abbrev TailInputSpace (k : ℕ) := BinaryNode → TailSamples k
abbrev TotalSizeSpace (k : ℕ) := BroadcastSpace × TailInputSpace k

noncomputable def tailInputMeasure (k : ℕ) (activity : ℝ) (ha : 0 < activity) : Measure (TailInputSpace k) :=
  Measure.infinitePi (fun _ : BinaryNode => tailSampleMeasure k activity ha)

instance (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    IsProbabilityMeasure (tailInputMeasure k activity ha) := by
  unfold tailInputMeasure
  infer_instance

noncomputable def totalSizeMeasure (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    Measure (TotalSizeSpace k) := (broadcastMeasure p).prod (tailInputMeasure k activity ha)

instance (p : unitInterval) (k : ℕ) (activity : ℝ) (ha : 0 < activity) :
    IsProbabilityMeasure (totalSizeMeasure p k activity ha) := by
  unfold totalSizeMeasure
  infer_instance

/-- A root occupation chooses between the two independent path samples. -/
def selectedTailSize (k : ℕ) (i : Bool) (s : TailSamples k) : ℝ :=
  if i then s.2.val.card else s.1.val.card

theorem selectedTailSize_nonneg (k : ℕ) (i : Bool) (s : TailSamples k) :
    0 ≤ selectedTailSize k i s := by
  cases i <;> simp [selectedTailSize]

theorem selectedTailSize_le (k : ℕ) (i : Bool) (s : TailSamples k) :
    selectedTailSize k i s ≤ 2 * (k : ℝ) + 1 := by
  have h0 := independentConfiguration_size_le (pendantPath (2 * k + 1)).graph s.1
  have h1 := independentConfiguration_size_le (pendantPath (2 * k)).graph s.2
  rw [pendantPath_card] at h0 h1
  cases i <;> dsimp [selectedTailSize] <;> exact_mod_cast (by omega : _)

noncomputable def selectedTailMean (k : ℕ) (activity : ℝ) (i : Bool) : ℝ :=
  if i then pathMean (2 * k) activity else pathMean (2 * k + 1) activity

theorem integral_selectedTailSize (k : ℕ) (activity : ℝ) (ha : 0 < activity) (i : Bool) :
    ∫ s, selectedTailSize k i s ∂tailSampleMeasure k activity ha = selectedTailMean k activity i := by
  cases i <;> simp only [selectedTailSize, selectedTailMean, Bool.false_eq_true, ite_false, ite_true]
  · have h := integral_fun_fst
      (μ := (hardCore (pendantPath (2 * k + 1)).graph activity ha).toMeasure)
      (ν := (hardCore (pendantPath (2 * k)).graph activity ha).toMeasure)
      (fun s : IndependentConfiguration (pendantPath (2 * k + 1)).graph => (s.val.card : ℝ))
    simp only [probReal_univ, one_smul] at h
    rw [hardCore_expected_size, pathPolynomial_graph] at h
    exact h
  · have h := integral_fun_snd
      (μ := (hardCore (pendantPath (2 * k + 1)).graph activity ha).toMeasure)
      (ν := (hardCore (pendantPath (2 * k)).graph activity ha).toMeasure)
      (fun s : IndependentConfiguration (pendantPath (2 * k)).graph => (s.val.card : ℝ))
    simp only [probReal_univ, one_smul] at h
    rw [hardCore_expected_size, pathPolynomial_graph] at h
    exact h

/-- Total occupied vertices in the binary core and the conditionally selected leaf paths. -/
noncomputable def sampledTotalSize (k m : ℕ) (i : Bool) (ω : TotalSizeSpace k) : ℝ :=
  (∑ h ∈ range (m + 1), ∑ v ∈ binaryLevel h, boolIndicator (broadcastState i ω.1 v)) +
    ∑ v ∈ binaryLevel m, selectedTailSize k (broadcastState i ω.1 v) (ω.2 v)

end SphericalTreeFailures
