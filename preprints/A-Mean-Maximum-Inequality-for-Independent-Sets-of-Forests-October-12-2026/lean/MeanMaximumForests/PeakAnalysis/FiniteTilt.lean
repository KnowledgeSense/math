import HardCoreActivityThreshold.FiniteVariance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
variable {Ω : Type*} [Fintype Ω]

noncomputable def tiltMoment (μ : FiniteLaw Ω) (X f : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ x, μ.mass x * Real.exp (t * X x) * f x

noncomputable def tiltPartition (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  tiltMoment μ X (fun _ => 1) t

theorem tiltPartition_pos (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    0 < tiltPartition μ X t := by
  have he : ∃ x : Ω, 0 < μ.mass x := by
    by_contra h
    push Not at h
    have hz : ∀ x : Ω, μ.mass x = 0 := fun x => le_antisymm (h x) (μ.nonneg x)
    have hs := μ.sum_one
    simp only [hz, sum_const_zero] at hs
    norm_num at hs
  obtain ⟨x, hx⟩ := he
  unfold tiltPartition tiltMoment
  apply sum_pos'
  · intro y _
    positivity [μ.nonneg y]
  · exact ⟨x, mem_univ x, by positivity⟩

noncomputable def finiteTilt (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) : FiniteLaw Ω :=
  μ.reweight (fun x => Real.exp (t * X x)) (fun x => (Real.exp_pos _).le)
    (by simpa only [FiniteLaw.expectation, tiltPartition, tiltMoment, mul_one] using tiltPartition_pos μ X t)

theorem finiteTilt_expectation (μ : FiniteLaw Ω) (X f : Ω → ℝ) (t : ℝ) :
    (finiteTilt μ X t).expectation f = tiltMoment μ X f t / tiltPartition μ X t := by
  simp only [finiteTilt, FiniteLaw.reweight, FiniteLaw.expectation, tiltPartition, tiltMoment,
    mul_one, div_mul_eq_mul_div, ← sum_div]

theorem tiltMoment_hasDerivAt (μ : FiniteLaw Ω) (X f : Ω → ℝ) (t : ℝ) :
    HasDerivAt (tiltMoment μ X f) (tiltMoment μ X (fun x => X x * f x) t) t := by
  unfold tiltMoment
  have h := HasDerivAt.sum (u := univ) (fun x _ =>
    (((hasDerivAt_id t).mul_const (X x)).exp.const_mul (μ.mass x)).mul_const (f x))
  convert h using 1
  · funext s
    simp only [Finset.sum_apply, id_eq]
  · apply sum_congr rfl
    intro x _
    simp only [id_eq, one_mul]
    ring

theorem tiltPartition_hasDerivAt (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (tiltPartition μ X) (tiltMoment μ X X t) t := by
  change HasDerivAt (tiltMoment μ X (fun _ => 1)) (tiltMoment μ X X t) t
  simpa only [mul_one] using tiltMoment_hasDerivAt μ X (fun _ => 1) t

/-- The log-activity derivative of the actual tilted mean is exactly its variance. -/
theorem finiteTilt_mean_hasDerivAt (μ : FiniteLaw Ω) (X : Ω → ℝ) (t : ℝ) :
    HasDerivAt (fun s => (finiteTilt μ X s).expectation X) ((finiteTilt μ X t).variance X) t := by
  have h := (tiltMoment_hasDerivAt μ X X t).div (tiltPartition_hasDerivAt μ X t)
    (tiltPartition_pos μ X t).ne'
  simp_rw [finiteTilt_expectation]
  convert h using 1
  rw [FiniteLaw.variance_eq_second_moment, finiteTilt_expectation, finiteTilt_expectation]
  simp only [← pow_two]
  field_simp

end MeanMaximumForests.PeakAnalysis
