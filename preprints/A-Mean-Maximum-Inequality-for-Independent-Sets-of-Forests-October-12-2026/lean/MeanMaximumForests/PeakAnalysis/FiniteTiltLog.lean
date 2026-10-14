import MeanMaximumForests.PeakAnalysis.FiniteTilt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold
variable {Ω : Type*} [Fintype Ω]

@[simp] theorem tiltPartition_zero (μ : FiniteLaw Ω) (X : Ω → ℝ) : tiltPartition μ X 0 = 1 := by
  simp only [tiltPartition, tiltMoment, zero_mul, Real.exp_zero, mul_one, μ.sum_one]

theorem finiteTilt_log_partition_hasDerivAt (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (fun s => Real.log (tiltPartition μ X s)) ((finiteTilt μ X t).expectation X) t := by
  rw [finiteTilt_expectation]
  exact (tiltPartition_hasDerivAt μ X t).log (tiltPartition_pos μ X t).ne'

/-- Lower occupation along a negative tilt forces an exponentially small partition ratio. -/
theorem tiltPartition_le_exp_of_mean_lower (μ : FiniteLaw Ω) (X : Ω → ℝ) (t c : ℝ) (ht : t ≤ 0)
    (hm : ∀ s ∈ Set.Icc t 0, c ≤ (finiteTilt μ X s).expectation X) :
    tiltPartition μ X t ≤ Real.exp (c * t) := by
  let f := fun s => Real.log (tiltPartition μ X s)
  have hd : Differentiable ℝ f := fun s => (finiteTilt_log_partition_hasDerivAt μ X s).differentiableAt
  have hder : ∀ s ∈ interior (Set.Icc t 0), c ≤ deriv f s := by
    intro s hs
    rw [(finiteTilt_log_partition_hasDerivAt μ X s).deriv]
    exact hm s (interior_subset hs)
  have h := (convex_Icc t 0).mul_sub_le_image_sub_of_le_deriv hd.continuous.continuousOn
    hd.differentiableOn hder t ⟨le_rfl, ht⟩ 0 ⟨ht, le_rfl⟩ ht
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at h
  have hlog : Real.log (tiltPartition μ X t) ≤ c * t := by change c * (0 - t) ≤ 0 - _ at h; linarith
  have he := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (tiltPartition_pos μ X t)] at he

end MeanMaximumForests.PeakAnalysis
