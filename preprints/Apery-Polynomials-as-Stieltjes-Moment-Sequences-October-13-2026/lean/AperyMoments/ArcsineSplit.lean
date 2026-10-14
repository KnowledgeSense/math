import AperyMoments.ArcsineConvolution
import AperyMoments.ArcsineSubstitution

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def arcsineHalfWeight (b a v : ℝ) : ℝ :=
  (b - a) * (b - a) ^ (-(1 / 2 : ℝ)) *
    (b + a + (b - a) * v) ^ (-(1 / 2 : ℝ)) * (1 - v) ^ (-(1 / 2 : ℝ))

theorem arcsineHalfWeight_jacobian {b a v : ℝ} (hl : -b < a) (hr : a < b)
    (hv : v ∈ Ioo 0 1) :
    (b - a) * (Real.sqrt (b ^ 2 - (a + (b - a) * v) ^ 2))⁻¹ =
      arcsineHalfWeight b a v := by
  have ha : 0 < b - a := sub_pos.mpr hr
  have hc : 0 < b + a + (b - a) * v := by nlinarith [mul_pos ha hv.1]
  have hd : 0 < 1 - v := by linarith [hv.2]
  have he : b ^ 2 - (a + (b - a) * v) ^ 2 =
      ((b - a) * (1 - v)) * (b + a + (b - a) * v) := by ring
  rw [← inverse_sqrt_rpow (by rw [he]; positivity), he,
    Real.mul_rpow (mul_nonneg ha.le hd.le) hc.le, Real.mul_rpow ha.le hd.le]
  unfold arcsineHalfWeight
  ring

theorem arcsine_right_half {b a : ℝ} (hl : -b < a) (hr : a < b) (F : ℝ → ℂ) :
    (∫ u in a..b, (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) =
      ∫ v in (0 : ℝ)..1, arcsineHalfWeight b a v • F (a + (b - a) * v) := by
  have he := intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) (b - a) a
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel] at he
  rw [← he, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ v : ℝ ∂volume, v ≠ 1 := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (1 : ℝ) : volume {(1 : ℝ)} = 0)
  filter_upwards [hne] with v hv1 hv
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  rw [smul_smul, arcsineHalfWeight_jacobian hl hr ⟨hv.1, lt_of_le_of_ne hv.2 hv1⟩]

theorem arcsine_left_half {b a : ℝ} (hl : -b < a) (hr : a < b) (F : ℝ → ℂ) :
    (∫ u in (-b)..a, (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) =
      ∫ v in (0 : ℝ)..1, arcsineHalfWeight b (-a) v • F (a - (b + a) * v) := by
  have he := intervalIntegral.integral_comp_neg (a := -a) (b := b)
    (fun u : ℝ => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u)
  simp only [neg_neg, neg_sq] at he
  rw [← he, arcsine_right_half (by linarith : -b < -a) (by linarith : -a < b)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [show -(-a + (b - -a) * v) = a - (b + a) * v by ring]

theorem arcsineHalfWeight_nonneg {b a v : ℝ} (hl : -b < a) (hr : a < b)
    (hv : v ∈ Icc 0 1) : 0 ≤ arcsineHalfWeight b a v := by
  have ha : 0 < b - a := sub_pos.mpr hr
  have hc : 0 < b + a + (b - a) * v := by nlinarith [mul_nonneg ha.le hv.1]
  unfold arcsineHalfWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg ha.le _))
    (Real.rpow_nonneg hc.le _)) (Real.rpow_nonneg (by linarith [hv.2]) _)

theorem arcsineHalfWeight_bound {b a v δ R : ℝ} (hδ : 0 < δ)
    (ha : δ ≤ b - a) (hb : δ ≤ b + a) (hR : b - a ≤ R) (hv : v ∈ Ioo 0 1) :
    arcsineHalfWeight b a v ≤
      (R * δ ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ))) * (1 - v) ^ (-(1 / 2 : ℝ)) := by
  have ha0 : 0 < b - a := hδ.trans_le ha
  have hR0 : 0 < R := ha0.trans_le hR
  have hb0 : 0 < b + a + (b - a) * v := by nlinarith [mul_pos ha0 hv.1]
  have hp := Real.rpow_le_rpow_of_nonpos hδ ha (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  have hq := Real.rpow_le_rpow_of_nonpos hδ
    (show δ ≤ b + a + (b - a) * v by nlinarith [mul_pos ha0 hv.1])
    (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  unfold arcsineHalfWeight
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith [hv.2]) _)
  apply mul_le_mul (mul_le_mul hR hp (Real.rpow_nonneg ha0.le _) (by linarith)) hq
    (Real.rpow_nonneg hb0.le _) (by positivity)

theorem arcsine_split {b a : ℝ} (hb : 0 < b) (hl : -b < a) (hr : a < b)
    (F : ℝ → ℂ) (hi : IntervalIntegrable (fun θ => F (b * Real.cos θ)) volume 0 Real.pi) :
    (∫ θ in (0 : ℝ)..Real.pi, F (b * Real.cos θ)) =
      (∫ v in (0 : ℝ)..1, arcsineHalfWeight b (-a) v • F (a - (b + a) * v)) +
      (∫ v in (0 : ℝ)..1, arcsineHalfWeight b a v • F (a + (b - a) * v)) := by
  have hu := (arcsine_integrable_iff hb F).mpr hi
  have hu' : IntervalIntegrable (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) volume (-b) b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr hu
  have hul := hu'.mono_set (show uIcc (-b) a ⊆ uIcc (-b) b by
    rw [uIcc_of_le hl.le, uIcc_of_le (by linarith : -b ≤ b)]
    exact Icc_subset_Icc le_rfl hr.le)
  have hur := hu'.mono_set (show uIcc a b ⊆ uIcc (-b) b by
    rw [uIcc_of_le hr.le, uIcc_of_le (by linarith : -b ≤ b)]
    exact Icc_subset_Icc hl.le le_rfl)
  rw [← arcsine_integral_substitution hb, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : -b ≤ b),
    ← intervalIntegral.integral_add_adjacent_intervals hul hur,
    arcsine_left_half hl hr, arcsine_right_half hl hr]

theorem arcsine_right_half_integrable_iff {b a : ℝ} (hl : -b < a) (hr : a < b) (F : ℝ → ℂ) :
    IntervalIntegrable (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u) volume a b ↔
      IntervalIntegrable (fun v => arcsineHalfWeight b a v • F (a + (b - a) * v)) volume 0 1 := by
  have ha : 0 < b - a := sub_pos.mpr hr
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioo (0 : ℝ) 1) (f := fun v : ℝ => (b - a) * v + a) (f' := fun _ => b - a)
    measurableSet_Ioo (fun v _ => by simpa only [mul_one, id_eq] using (((hasDerivAt_id v).const_mul (b - a)).add_const a).hasDerivWithinAt)
    (fun _ _ _ _ he => mul_left_cancel₀ ha.ne' (add_right_cancel he))
    (fun u : ℝ => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • F u)
  rw [image_affine_Ioo ha, mul_zero, zero_add, mul_one, sub_add_cancel] at hi
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le,
    intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply hi.trans
  apply integrableOn_congr_fun _ measurableSet_Ioo
  intro v hv
  dsimp only
  rw [abs_of_pos ha, add_comm ((b - a) * v) a, smul_smul, arcsineHalfWeight_jacobian hl hr hv]

end AperyMoments
