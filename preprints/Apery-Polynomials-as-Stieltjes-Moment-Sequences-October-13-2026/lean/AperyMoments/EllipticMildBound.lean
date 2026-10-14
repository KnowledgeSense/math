import AperyMoments.EllipticNorm

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem ellipticK_mild_bound {m : ℝ} (hm : m < 1) :
    ellipticK m ≤ 8 * (1 - m) ^ (-(1 / 16 : ℝ)) := by
  have hp : 0 < 1 - m := sub_pos.mpr hm
  have h := ellipticK_complement_eighth_bound (Real.sqrt_pos.mpr hp)
  rw [Real.sq_sqrt hp.le, sub_sub_cancel] at h
  have he : (Real.sqrt (1 - m)) ^ (-(1 / 8 : ℝ)) = (1 - m) ^ (-(1 / 16 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hp.le]
    norm_num
  rwa [he] at h

theorem ellipticK_cut_mild_bound {m : ℝ} (hm : 1 < m) :
    m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ + ellipticK (1 - m) ≤
      8 * (m - 1) ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < m - 1 := by linarith
  have hmi : m⁻¹ < 1 := (inv_lt_one₀ hm0).mpr hm
  have h := mul_le_mul_of_nonneg_left (ellipticK_mild_bound hmi)
    (Real.rpow_nonneg hm0.le (-(1 / 2 : ℝ)))
  have he : m ^ (-(1 / 2 : ℝ)) * (1 - m⁻¹) ^ (-(1 / 16 : ℝ)) =
      m ^ (-(7 / 16 : ℝ)) * (m - 1) ^ (-(1 / 16 : ℝ)) := by
    rw [show 1 - m⁻¹ = (m - 1) * m⁻¹ by field_simp,
      Real.mul_rpow hp.le (inv_nonneg.mpr hm0.le), Real.inv_rpow hm0.le,
      ← Real.rpow_neg hm0.le]
    rw [mul_left_comm, ← Real.rpow_add hm0]
    norm_num
    ring
  have hpow : m ^ (-(7 / 16 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hm.le
      (by norm_num : -(7 / 16 : ℝ) ≤ 0)
  have hscale : m ^ (-(1 / 2 : ℝ)) * ellipticK m⁻¹ ≤ 8 * (m - 1) ^ (-(1 / 16 : ℝ)) := by
    calc
      _ ≤ 8 * (m ^ (-(1 / 2 : ℝ)) * (1 - m⁻¹) ^ (-(1 / 16 : ℝ))) := by nlinarith [h]
      _ = 8 * (m ^ (-(7 / 16 : ℝ)) * (m - 1) ^ (-(1 / 16 : ℝ))) := by rw [he]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le (-(1 / 16 : ℝ)))]
  have hlow := ellipticK_mono (show 1 - m ≤ 0 by linarith) (by norm_num : (0 : ℝ) < 1)
  rw [ellipticK_zero] at hlow
  linarith

theorem complexEllipticK_re_mild_bound {z : ℂ} (hz : z.im < 0) (hne : z.re ≠ 1) :
    ‖complexEllipticK z‖ ≤ 8 * |1 - z.re| ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hb := (complexEllipticK_re_bound_below h).trans (ellipticK_mild_bound h)
    rw [abs_of_pos (sub_pos.mpr h)]
    linarith [Real.pi_pos]
  · have hb := complexEllipticK_vertical_norm_bound_above h (neg_pos.mpr hz)
    have he : (z.re : ℂ) - Complex.I * (-z.im : ℝ) = z := by apply Complex.ext <;> simp
    rw [he] at hb
    have ha : |1 - z.re| = z.re - 1 := by rw [abs_of_neg (by linarith : 1 - z.re < 0)]; ring
    rw [ha]
    exact hb.trans (ellipticK_cut_mild_bound h)

end AperyMoments
