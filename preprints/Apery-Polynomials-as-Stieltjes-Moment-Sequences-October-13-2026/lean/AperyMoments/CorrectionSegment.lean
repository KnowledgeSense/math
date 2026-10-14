import AperyMoments.CorrectionHolomorphy
import AperyMoments.LowerEllipticInversion

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def correctionSegmentPoint (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  w + ((b : ℂ) - w) * (v : ℂ)

/-- The original oriented segment integral, with the two principal square roots retained. -/
def segmentCorrection (b : ℝ) (w : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ v in (0 : ℝ)..1,
    complexEllipticK ((w - correctionSegmentPoint b w v) ^ 2 / 16) /
      (Complex.sqrt ((b : ℂ) - correctionSegmentPoint b w v) *
        Complex.sqrt ((b : ℂ) + correctionSegmentPoint b w v)) * ((b : ℂ) - w)

theorem inverse_complex_sqrt (z : ℂ) :
    (Complex.sqrt z)⁻¹ = z ^ (-(1 / 2 : ℂ)) := by
  rw [Complex.cpow_neg, Complex.sqrt]
  norm_num

theorem correction_segment_integrand (b : ℝ) (w : ℂ) {v : ℝ} (hv : v < 1) :
    complexEllipticK ((w - correctionSegmentPoint b w v) ^ 2 / 16) /
      (Complex.sqrt ((b : ℂ) - correctionSegmentPoint b w v) *
        Complex.sqrt ((b : ℂ) + correctionSegmentPoint b w v)) * ((b : ℂ) - w) =
      (((b : ℂ) - w) * (((b : ℂ) - w) ^ (-(1 / 2 : ℂ)))) *
        (correctionRegular b w v * (correctionWeight v : ℂ)) := by
  have hp : (w - correctionSegmentPoint b w v) ^ 2 / 16 = correctionParameter b w v := by
    unfold correctionSegmentPoint correctionParameter
    ring
  have ha : (b : ℂ) - correctionSegmentPoint b w v =
      ((1 - v : ℝ) : ℂ) * ((b : ℂ) - w) := by
    unfold correctionSegmentPoint
    push_cast
    ring
  have hb : (b : ℂ) + correctionSegmentPoint b w v = correctionBase b w v := by
    unfold correctionSegmentPoint correctionBase
    push_cast
    ring
  rw [hp, div_eq_mul_inv, mul_inv, inverse_complex_sqrt, inverse_complex_sqrt,
    ha, hb, inverse_sqrt_cpow_pos_mul (by linarith : 0 < 1 - v)]
  unfold correctionRegular correctionWeight
  ring

/-- The extracted endpoint-weight formula is exactly the source's oriented path integral. -/
theorem continuedCorrection_eq_segmentCorrection (b : ℝ) (w : ℂ) :
    continuedCorrection b w = segmentCorrection b w := by
  unfold continuedCorrection segmentCorrection
  have he : (∫ v in (0 : ℝ)..1,
      complexEllipticK ((w - correctionSegmentPoint b w v) ^ 2 / 16) /
        (Complex.sqrt ((b : ℂ) - correctionSegmentPoint b w v) *
          Complex.sqrt ((b : ℂ) + correctionSegmentPoint b w v)) * ((b : ℂ) - w)) =
      (((b : ℂ) - w) * (((b : ℂ) - w) ^ (-(1 / 2 : ℂ)))) *
        ∫ v in (0 : ℝ)..1, correctionRegular b w v * (correctionWeight v : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ v : ℝ ∂volume, v ≠ 1 := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (1 : ℝ) : volume {(1 : ℝ)} = 0)
    filter_upwards [hne] with v hvne hv
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    exact correction_segment_integrand b w (lt_of_le_of_ne hv.2 hvne)
  rw [he]
  ring

end AperyMoments
