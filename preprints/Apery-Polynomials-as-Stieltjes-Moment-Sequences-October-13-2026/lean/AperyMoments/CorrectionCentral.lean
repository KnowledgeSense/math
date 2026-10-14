import AperyMoments.CorrectionSegment

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

def centralCorrection (b w : ℝ) : ℝ :=
  (b - w) * (b - w) ^ (-(1 / 2 : ℝ)) / Real.pi *
    ∫ v in (0 : ℝ)..1,
      ellipticK (((w - b) * v / 4) ^ 2) *
        (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v

theorem correctionDomain_central_mem {b w : ℝ} (hb2 : b ≤ 2)
    (hl : -b < w) (hr : w < b) : (w : ℂ) ∈ correctionDomain b := by
  right
  refine ⟨hl, hr, ?_⟩
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : w - b < 0)]
  linarith

theorem correctionRegular_ofReal {b w v : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < w) (hr : w < b) (hv : v ∈ Icc 0 1) :
    correctionRegular b (w : ℂ) v =
      ((ellipticK (((w - b) * v / 4) ^ 2) *
        (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hp : correctionParameter b (w : ℂ) v = ((((w - b) * v / 4) ^ 2 : ℝ) : ℂ) := by
    unfold correctionParameter
    push_cast
    rfl
  have hB : correctionBase b (w : ℂ) v = ((b * (1 + v) + w * (1 - v) : ℝ) : ℂ) := by
    unfold correctionBase
    push_cast
    rfl
  have hm := correctionParameter_mem_domain_of_mem (correctionDomain_central_mem hb2 hl hr) hv
  rw [hp] at hm
  have hm1 : ((w - b) * v / 4) ^ 2 < 1 := hm.resolve_left (by simp only [Complex.ofReal_im, ne_eq, not_not])
  have hbase := Complex.mem_slitPlane_iff.mp (correctionBase_mem_slitPlane_central (w := (w : ℂ)) hb hl hv)
  rw [hB] at hbase
  have hb0 : 0 < b * (1 + v) + w * (1 - v) := hbase.resolve_right (by simp)
  unfold correctionRegular
  rw [hp, hB, complexEllipticK_ofReal hm1, inverse_sqrt_cpow_of_nonneg hb0.le, Complex.ofReal_mul]

theorem continuedCorrection_central_value {b w : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < w) (hr : w < b) :
    continuedCorrection b (w : ℂ) = (centralCorrection b w : ℂ) := by
  unfold continuedCorrection centralCorrection
  rw [← Complex.ofReal_sub, inverse_sqrt_cpow_of_nonneg (by linarith : 0 ≤ b - w)]
  have he : (∫ v in (0 : ℝ)..1, correctionRegular b (w : ℂ) v * (correctionWeight v : ℂ)) =
      ((∫ v in (0 : ℝ)..1,
        ellipticK (((w - b) * v / 4) ^ 2) *
          (b * (1 + v) + w * (1 - v)) ^ (-(1 / 2 : ℝ)) * correctionWeight v : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    dsimp only
    rw [correctionRegular_ofReal hb hb2 hl hr hv, Complex.ofReal_mul]
    push_cast
    rfl
  rw [he]
  push_cast
  rfl

theorem continuedCorrection_central_boundary {b w : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < w) (hr : w < b) :
    Tendsto (continuedCorrection b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (centralCorrection b w : ℂ)) := by
  rw [← continuedCorrection_central_value hb hb2 hl hr]
  exact (continuedCorrection_differentiableAt hb
    (correctionDomain_central_mem hb2 hl hr)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

end AperyMoments
