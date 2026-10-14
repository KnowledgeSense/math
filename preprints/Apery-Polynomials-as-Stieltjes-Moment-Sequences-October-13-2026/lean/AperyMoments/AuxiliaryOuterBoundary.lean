import AperyMoments.CorrectionKappaValue
import AperyMoments.AuxiliaryRightBoundary

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

/-- The unrestricted boundary of the continued auxiliary function on the outer real cut. -/
theorem continuedAuxiliary_right_boundary {b w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b + 4) :
    Tendsto (continuedAuxiliary b) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 ((continuedDensity b w : ℂ) + rightCorrectionComplex b w / ((Real.pi ^ 2 : ℝ) : ℂ))) := by
  have hc := continuedCorrection_right_boundary hb hw hne
  rw [continuedCorrection_right_complex_value hb hw] at hc
  have h := (continuedSpectral_positive_boundary hb.le hw).sub
    ((hc.const_mul Complex.I).div_const ((Real.pi ^ 2 : ℝ) : ℂ))
  have he : (continuedDensity b w : ℂ) - Complex.I * (Complex.I * rightCorrectionComplex b w) /
      ((Real.pi ^ 2 : ℝ) : ℂ) =
      (continuedDensity b w : ℂ) + rightCorrectionComplex b w / ((Real.pi ^ 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  rw [he] at h
  unfold continuedAuxiliary
  exact h

/-- The real boundary value is exactly the two positive real integrals in the source. -/
theorem continuedAuxiliary_right_real_boundary {b w : ℝ} (hb : 0 < b) (hw : b < w)
    (hne : w ≠ b + 4) :
    Tendsto (fun z => (continuedAuxiliary b z).re) (𝓝[{z : ℂ | z.im < 0}] (w : ℂ))
      (𝓝 (continuedDensity b w + continuationCorrection b w)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (continuedAuxiliary_right_boundary hb hw hne)
  have he : ((continuedDensity b w : ℂ) + rightCorrectionComplex b w /
      ((Real.pi ^ 2 : ℝ) : ℂ)).re = continuedDensity b w + continuationCorrection b w := by
    rw [Complex.add_re, Complex.ofReal_re, div_eq_mul_inv, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [rightCorrectionComplex_re hb hw hne]
    field_simp
  rw [he] at h
  exact h

end AperyMoments
