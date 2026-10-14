import AperyMoments.EllipticBounds
import AperyMoments.CandidateDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def angularDensityBound (b : ℝ) : ℝ :=
  8 * (b/(2*Real.pi^2)) ^ (-(1/8 : ℝ)) / (2*Real.pi^2)

def continuedDensityBound (b : ℝ) : ℝ :=
  Real.pi⁻¹ * (angularDensityBound b * ∫ θ in (0 : ℝ)..Real.pi, θ ^ (-(1/4 : ℝ)))

theorem angularDensityBound_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ angularDensityBound b := by
  unfold angularDensityBound
  positivity

theorem continuedDensityBound_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ continuedDensityBound b := by
  have hi : 0 ≤ ∫ θ in (0 : ℝ)..Real.pi, θ ^ (-(1/4 : ℝ)) := by
    apply intervalIntegral.integral_nonneg Real.pi_pos.le
    intro θ hθ
    exact Real.rpow_nonneg hθ.1 _
  unfold continuedDensityBound
  exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (mul_nonneg (angularDensityBound_nonneg hb) hi)

theorem angular_latticeExpression_bound {b w θ : ℝ} (hb : 0 < b) (hw : b ≤ w)
    (hθ : θ ∈ Ioo 0 Real.pi) : latticeExpression (w-b*Real.cos θ) ≤
      angularDensityBound b * θ ^ (-(1/4 : ℝ)) := by
  let A := b/(2*Real.pi^2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hcos := Real.cos_le_one_sub_mul_cos_sq (show |θ| ≤ Real.pi by rw [abs_of_pos hθ.1]; exact hθ.2.le)
  have hmul := mul_le_mul_of_nonneg_left hcos hb.le
  have heA : 4*A = b*(2/Real.pi^2) := by dsimp [A]; ring
  have hc : A*θ^2 ≤ (w-b*Real.cos θ)/4 := by nlinarith
  have hcp : 0 < (w-b*Real.cos θ)/4 := lt_of_lt_of_le (mul_pos hA (sq_pos_of_pos hθ.1)) hc
  have hK := ellipticK_complement_eighth_bound hcp
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hA (sq_pos_of_pos hθ.1)) hc (by norm_num : -(1/8 : ℝ) ≤ 0)
  have he : (A*θ^2) ^ (-(1/8 : ℝ)) = A ^ (-(1/8 : ℝ)) * θ ^ (-(1/4 : ℝ)) := by
    rw [Real.mul_rpow hA.le (sq_nonneg θ), ← Real.rpow_natCast_mul hθ.1.le]
    norm_num
  rw [he] at hp
  have hm : 1-((w-b*Real.cos θ)/4)^2 = 1-(w-b*Real.cos θ)^2/16 := by ring
  rw [hm] at hK
  unfold latticeExpression angularDensityBound
  calc
    _ ≤ (8 * (A ^ (-(1/8 : ℝ)) * θ ^ (-(1/4 : ℝ)))) / (2*Real.pi^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact hK.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ = _ := by dsimp [A]; ring

theorem continuedDensity_uniform_bound {b w : ℝ} (hb : 0 < b) (hw : b < w) :
    continuedDensity b w ≤ continuedDensityBound b := by
  have hi := (shifted_latticeExpression_continuous hb.le hw).intervalIntegrable (μ := volume) 0 Real.pi
  have hpow : IntervalIntegrable (fun θ : ℝ => θ ^ (-(1/4 : ℝ))) volume 0 Real.pi :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le hi
    (IntervalIntegrable.const_mul hpow (angularDensityBound b))
    (fun θ hθ => angular_latticeExpression_bound hb hw.le hθ)
  rw [intervalIntegral.integral_const_mul] at hm
  exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr Real.pi_pos.le)

end AperyMoments
