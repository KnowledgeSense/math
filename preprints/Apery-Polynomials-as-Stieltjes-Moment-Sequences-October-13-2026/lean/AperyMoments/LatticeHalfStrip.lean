import AperyMoments.LatticeBounds
import AperyMoments.LatticeFourthPower

noncomputable section
namespace AperyMoments

def latticeHalfStripConstant : ℝ := ellipticK ((1/2 : ℝ)^2) / Real.pi^2

theorem latticeHalfStripConstant_nonneg : 0 ≤ latticeHalfStripConstant := by
  unfold latticeHalfStripConstant
  exact div_nonneg (ellipticK_pos (by norm_num)).le (sq_nonneg _)

theorem continuedLattice_halfStrip_bound {z : ℂ} (hz : z.im < 0)
    (hre : -2 ≤ z.re) (hne : z.re ≠ 0) :
    ‖continuedLattice z‖ ≤ latticeWeakConstant * |z.re|^(-(1/8 : ℝ)) + latticeHalfStripConstant := by
  have hh : ‖continuedLattice z‖ ≤
      (8*(|z.re|/4)^(-(1/8 : ℝ))+2*ellipticK ((1/2 : ℝ)^2))/(2*Real.pi^2) := by
    rcases lt_or_gt_of_ne hne with hn | hp
    · simpa only [show (2/4 : ℝ) = 1/2 by norm_num] using continuedLattice_strip_bound (by norm_num : (0 : ℝ)<2) (by norm_num) hz hne
        (by rw [abs_of_neg hn]; linarith)
    · have hv := lowerEllipticIntegral_positive_vertical_norm_bound
        (show 0 < z.re/4 by positivity) (show 0 < -z.im/4 by linarith)
      have he : ((z.re/4 : ℝ) : ℂ)-Complex.I*(-z.im/4 : ℝ) = z/4 := by
        apply Complex.ext <;> simp; ring
      rw [he] at hv
      unfold continuedLattice
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2*Real.pi^2)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hK := (ellipticK_pos (by norm_num : (1/2 : ℝ)^2 < 1)).le
      rw [abs_of_pos hp]
      linarith [ellipticK_complement_eighth_bound (show 0 < z.re/4 by positivity)]
  have he : (|z.re|/4)^(-(1/8 : ℝ)) =
      (4 : ℝ)^(1/8 : ℝ)*|z.re|^(-(1/8 : ℝ)) := by
    rw [Real.div_rpow (abs_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [he] at hh
  unfold latticeWeakConstant latticeHalfStripConstant
  convert hh using 1; ring

end AperyMoments
