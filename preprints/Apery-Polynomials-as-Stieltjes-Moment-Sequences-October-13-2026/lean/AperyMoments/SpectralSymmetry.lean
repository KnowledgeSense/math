import AperyMoments.CandidateDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem latticeDensity_neg (x : ℝ) : latticeDensity (-x) = latticeDensity x := by
  simp [latticeDensity, latticeExpression]

theorem spectralDensity_neg (b a : ℝ) : spectralDensity b (-a) = spectralDensity b a := by
  unfold spectralDensity
  congr 1
  have he := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi)
    (fun θ : ℝ => latticeDensity (a - b * Real.cos θ)) Real.pi
  simp only [sub_self, sub_zero] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [Real.cos_pi_sub]
  rw [show -a - b * Real.cos θ = -(a - b * -Real.cos θ) by ring, latticeDensity_neg]

end AperyMoments
