import AperyMoments.EllipticCutParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def cutAngle (m : ℝ) : ℝ := Real.arcsin (Real.sqrt m)⁻¹

theorem cutAngle_mem_Ioo {m : ℝ} (hm : 1 < m) : cutAngle m ∈ Ioo 0 (Real.pi / 2) := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ m)
  have hp := Real.sqrt_nonneg m
  have h1 : 1 < Real.sqrt m := by nlinarith
  exact ⟨Real.arcsin_pos.mpr (inv_pos.mpr (by linarith)),
    Real.arcsin_lt_pi_div_two.mpr ((inv_lt_one₀ (by linarith)).mpr h1)⟩

theorem elliptic_cut_threshold {m θ : ℝ} (hm : 1 < m) (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    0 ≤ 1 - m * Real.sin θ ^ 2 ↔ θ ≤ cutAngle m := by
  have hm0 : 0 < m := by linarith
  have hr := Real.sqrt_pos.mpr hm0
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
  have h1 : 1 < Real.sqrt m := by nlinarith [Real.sq_sqrt hm0.le]
  have hk : (Real.sqrt m)⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr h1.le
  have hb : 0 ≤ 1 - m * Real.sin θ ^ 2 ↔ Real.sqrt m * Real.sin θ ≤ 1 := by
    calc
      0 ≤ 1 - m * Real.sin θ ^ 2 ↔ m * Real.sin θ ^ 2 ≤ 1 := sub_nonneg
      _ ↔ (Real.sqrt m * Real.sin θ) ^ 2 ≤ (1 : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hm0.le, one_pow]
      _ ↔ Real.sqrt m * Real.sin θ ≤ 1 := sq_le_sq₀ (mul_nonneg hr.le hs) zero_le_one
  rw [hb]
  have he : Real.sqrt m * Real.sin θ ≤ 1 ↔ Real.sin θ ≤ (Real.sqrt m)⁻¹ := by
    rw [← one_div, le_div_iff₀ hr, mul_comm]
  rw [he, ← Real.sin_arcsin (by linarith [inv_pos.mpr hr]) hk]
  exact Real.strictMonoOn_sin.le_iff_le ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    (Real.arcsin_mem_Icc _)

theorem complexEllipticK_cut_re_interval {m : ℝ} (hm : 1 < m) :
    (complexEllipticK m).re = ∫ θ in (0:ℝ)..cutAngle m,
      (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rw [complexEllipticK_cut_re hm]
  calc
    _ = ∫ θ in (0:ℝ)..Real.pi / 2,
        {θ | θ ≤ cutAngle m}.indicator
          (fun θ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ))) θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le (by positivity)] at hθ
      simp only [Set.indicator, mem_ofPred_eq, elliptic_cut_threshold hm hθ]
    _ = _ := intervalIntegral.integral_indicator
      ⟨(cutAngle_mem_Ioo hm).1.le, (cutAngle_mem_Ioo hm).2.le⟩

end AperyMoments
