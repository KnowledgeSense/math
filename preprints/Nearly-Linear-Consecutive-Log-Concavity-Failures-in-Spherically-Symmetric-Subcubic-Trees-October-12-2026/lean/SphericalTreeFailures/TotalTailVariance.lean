import SphericalTreeFailures.TailVariance

set_option backward.isDefEq.respectTransparency false

namespace SphericalTreeFailures
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem measurable_tailNoise (k m : ℕ) (activity : ℝ) (i : Bool) :
    Measurable (tailNoise k m activity i) := by
  unfold tailNoise
  apply Finset.measurable_sum
  intro v _
  exact (measurable_of_finite (fun s : Bool × TailSamples k =>
    tailSampleNoise k activity s.1 s.2)).comp
      (((measurable_broadcastState i v).comp measurable_fst).prodMk
        ((measurable_pi_apply v).comp measurable_snd))

theorem tailNoise_abs_le (k m : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) (ω : TotalSizeSpace k) :
    |tailNoise k m activity i ω| ≤ (2 : ℝ) ^ m * (2 * (k : ℝ) + 1) := by
  unfold tailNoise
  calc
    _ ≤ ∑ v ∈ binaryLevel m, |tailSampleNoise k activity (broadcastState i ω.1 v) (ω.2 v)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ binaryLevel m, (2 * (k : ℝ) + 1) :=
      sum_le_sum fun v _ => tailSampleNoise_abs_le k activity ha _ _
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_binaryLevel, Nat.cast_pow, Nat.cast_ofNat]

theorem memLp_tailNoise (p : unitInterval) (k m : ℕ) (activity : ℝ) (ha : 0 < activity)
    (i : Bool) (q : ℝ≥0∞) :
    MemLp (tailNoise k m activity i) q (totalSizeMeasure p k activity ha) := by
  apply MemLp.of_bound (measurable_tailNoise k m activity i).aestronglyMeasurable
    ((2 : ℝ) ^ m * (2 * (k : ℝ) + 1))
  exact ae_of_all _ fun ω => tailNoise_abs_le k m activity ha i ω

theorem total_tail_variance_bound (p : unitInterval) (k m : ℕ) (activity : ℝ)
    (ha : 0 < activity) (i : Bool) :
    ∫ ω, tailNoise k m activity i ω ^ 2 ∂totalSizeMeasure p k activity ha ≤
      (2 : ℝ) ^ m * (2 * (k : ℝ) + 1) ^ 2 := by
  have hInt : Integrable (fun ω => tailNoise k m activity i ω ^ 2)
      (totalSizeMeasure p k activity ha) := by
    convert (memLp_tailNoise p k m activity ha i 2).integrable_mul
      (memLp_tailNoise p k m activity ha i 2) using 1
    ext ω
    exact pow_two _
  rw [totalSizeMeasure, integral_prod _ hInt]
  have hinner (ω : BroadcastSpace) :
      (∫ τ, tailNoise k m activity i (ω, τ) ^ 2 ∂tailInputMeasure k activity ha) ≤
        (2 : ℝ) ^ m * (2 * (k : ℝ) + 1) ^ 2 := by
    have h := tail_sum_variance_bound k activity ha (binaryLevel m) (broadcastState i ω)
    simpa only [tailNoise, card_binaryLevel, Nat.cast_pow, Nat.cast_ofNat] using h
  have h := integral_mono hInt.integral_prod_left (integrable_const _) hinner
  simpa using h

end SphericalTreeFailures
