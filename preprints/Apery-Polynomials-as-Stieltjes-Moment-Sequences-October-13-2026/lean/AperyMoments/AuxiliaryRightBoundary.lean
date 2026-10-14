import AperyMoments.CorrectionRightValue
import AperyMoments.SpectralCentralBoundary

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem continuedAuxiliary_right_boundary_before_cut {b w : ℝ} (hb : 0 < b)
    (hw : b < w) (hw4 : w < b + 4) :
    Tendsto (continuedAuxiliary b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 ((continuedDensity b w + continuationCorrection b w : ℝ) : ℂ)) := by
  have hc := continuedCorrection_right_boundary_before_cut hb hw hw4
  rw [continuedCorrection_right_value_before_cut hb hw hw4] at hc
  have h := (continuedSpectral_positive_boundary hb.le hw).sub
    ((hc.const_mul Complex.I).div_const ((Real.pi ^ 2 : ℝ) : ℂ))
  have he : (continuedDensity b w : ℂ) - Complex.I * (Complex.I * (rightCorrectionReal b w : ℂ)) /
      ((Real.pi ^ 2 : ℝ) : ℂ) = ((continuedDensity b w + continuationCorrection b w : ℝ) : ℂ) := by
    rw [continuationCorrection_before_cut hb hw hw4, ← mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  rw [he] at h
  unfold continuedAuxiliary
  exact h

end AperyMoments
