import AperyMoments.LowerEllipticNorm
import AperyMoments.LatticeContinuation

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- Uniform integrable power control, retaining the genuine lower continuation. -/
theorem lowerEllipticIntegral_strip_bound {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    {z : ℂ} (hz : z.im < 0) (hne : z.re ≠ 0) (hbound : |z.re| ≤ R) :
    ‖lowerEllipticIntegral z‖ ≤ 8 * |z.re| ^ (-(1 / 8 : ℝ)) + 2 * ellipticK (R ^ 2) := by
  have hR2 : R ^ 2 < 1 := by nlinarith
  have hK : 0 < ellipticK (R ^ 2) := ellipticK_pos hR2
  have he : z = (z.re : ℂ) - Complex.I * (-z.im : ℝ) := by
    apply Complex.ext <;> simp
  have hε : 0 < -z.im := neg_pos.mpr hz
  rcases lt_or_gt_of_ne hne with hc | hc
  · have hc0 : 0 < -z.re := neg_pos.mpr hc
    have hc1 : -z.re < 1 := by simpa [abs_of_neg hc] using hbound.trans_lt hR1
    have hv := lowerEllipticIntegral_negative_vertical_norm_bound hc0 hc1 hε
    have he' : -(↑(-z.re) : ℂ) - Complex.I * (-z.im : ℝ) = z := by apply Complex.ext <;> simp
    rw [he'] at hv
    have hm : (-z.re) ^ 2 ≤ R ^ 2 := by rw [abs_of_neg hc] at hbound; nlinarith
    have hmK := ellipticK_mono hm hR2
    have hpow := ellipticK_complement_eighth_bound hc0
    rw [abs_of_neg hc]
    linarith
  · have hv := lowerEllipticIntegral_positive_vertical_norm_bound hc hε
    rw [← he] at hv
    rw [abs_of_pos hc]
    linarith [ellipticK_complement_eighth_bound hc]

theorem continuedLattice_strip_bound {R : ℝ} (hR : 0 < R) (hR4 : R < 4)
    {z : ℂ} (hz : z.im < 0) (hne : z.re ≠ 0) (hbound : |z.re| ≤ R) :
    ‖continuedLattice z‖ ≤
      (8 * (|z.re| / 4) ^ (-(1 / 8 : ℝ)) + 2 * ellipticK ((R / 4) ^ 2)) /
        (2 * Real.pi ^ 2) := by
  have h := lowerEllipticIntegral_strip_bound (R := R / 4) (by positivity)
    (by linarith) (z := z / 4) (by simpa using div_neg_of_neg_of_pos hz (by norm_num : (0 : ℝ) < 4))
    (by simpa using div_ne_zero hne (by norm_num : (4 : ℝ) ≠ 0))
    (by simpa [abs_div] using div_le_div_of_nonneg_right hbound (by norm_num : (0 : ℝ) ≤ 4))
  unfold continuedLattice
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi ^ 2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [abs_div] using h

theorem continuedLattice_scaled_bound {δ R c v : ℝ} (hδ : 0 < δ) (hR4 : R < 4)
    (hc : δ ≤ c) (hcR : c ≤ R) (hv : v ∈ Ioo 0 1) {z : ℂ} (hz : z.im < 0)
    (hre : |z.re| = c * v) :
    ‖continuedLattice z‖ ≤
      ((8 * (δ / 4) ^ (-(1 / 8 : ℝ)) + 2 * ellipticK ((R / 4) ^ 2)) /
        (2 * Real.pi ^ 2)) * v ^ (-(1 / 8 : ℝ)) := by
  have hc0 := hδ.trans_le hc
  have hR0 := hc0.trans_le hcR
  have hcv := mul_pos hc0 hv.1
  have hne : z.re ≠ 0 := abs_pos.mp (hre.symm ▸ hcv)
  have hbound : |z.re| ≤ R := by rw [hre]; nlinarith [hv.2]
  have hh := continuedLattice_strip_bound hR0 hR4 hz hne hbound
  rw [hre, show c * v / 4 = (c / 4) * v by ring,
    Real.mul_rpow (by positivity : 0 ≤ c / 4) hv.1.le] at hh
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ / 4)
    (div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 4))
    (by norm_num : (-(1 / 8 : ℝ)) ≤ 0)
  have hpow : 1 ≤ v ^ (-(1 / 8 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos hv.1 hv.2.le
      (by norm_num : (-(1 / 8 : ℝ)) ≤ 0)
  have hK : 0 ≤ ellipticK ((R / 4) ^ 2) := (ellipticK_pos (by nlinarith : (R / 4) ^ 2 < 1)).le
  have hnum : 8 * ((c / 4) ^ (-(1 / 8 : ℝ)) * v ^ (-(1 / 8 : ℝ))) +
      2 * ellipticK ((R / 4) ^ 2) ≤
      (8 * (δ / 4) ^ (-(1 / 8 : ℝ)) + 2 * ellipticK ((R / 4) ^ 2)) * v ^ (-(1 / 8 : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hv.1.le (-(1 / 8 : ℝ))),
      mul_le_mul_of_nonneg_left hpow hK]
  calc
    _ ≤ _ := hh
    _ ≤ ((8 * (δ / 4) ^ (-(1 / 8 : ℝ)) + 2 * ellipticK ((R / 4) ^ 2)) *
        v ^ (-(1 / 8 : ℝ))) / (2 * Real.pi ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by ring

end AperyMoments
