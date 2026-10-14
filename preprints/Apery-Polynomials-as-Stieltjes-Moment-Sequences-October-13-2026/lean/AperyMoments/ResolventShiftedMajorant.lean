import AperyMoments.ResolventWeightedBound

noncomputable section
namespace AperyMoments

theorem weighted_inverse_third_bound {κ y x : ℝ} (hκ : 0 < κ) (hy : 0 < y)
    (hy1 : y ≤ 1) (hx : 0 < x) :
    y*(κ*y*x)^(-(1/3 : ℝ)) ≤ κ^(-(1/3 : ℝ))*x^(-(1/3 : ℝ)) := by
  have he : y*y^(-(1/3 : ℝ)) = y^(2/3 : ℝ) := by
    calc
      _ = y^(1 : ℝ)*y^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
      _ = y^((1 : ℝ)+-(1/3 : ℝ)) := (Real.rpow_add hy _ _).symm
      _ = _ := by norm_num
  rw [Real.mul_rpow (mul_nonneg hκ.le hy.le) hx.le, Real.mul_rpow hκ.le hy.le]
  have hpow : y^(2/3 : ℝ) ≤ 1 := Real.rpow_le_one hy.le hy1 (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hpow
    (mul_nonneg (Real.rpow_nonneg hκ.le (-(1/3 : ℝ))) (Real.rpow_nonneg hx.le (-(1/3 : ℝ))))
  rw [← he] at hh
  nlinarith

theorem momentTransform_shifted_majorant {α δ R : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hδ : 0 < δ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y t : ℝ, 0 < y → y ≤ α/2 → y ≤ 1 → δ ≤ t → t ≤ R →
      t ≠ horizontalCritical α y →
      |(momentTransform α ((t : ℂ)+y*Complex.I)).im|+
        y*‖momentTransform α ((t : ℂ)+y*Complex.I)‖ ≤
        C*(1+‖t-horizontalCritical α y‖^(-(1/3 : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := momentTransform_weighted_bound (N := R+1) hα hα1 hδ
  let κ := horizontalCriticalConstant α δ (R+1)
  have hκ : 0 < κ := horizontalCriticalConstant_pos hα hδ (by linarith)
  let P := κ^(-(1/3 : ℝ))
  have hP : 0 ≤ P := Real.rpow_nonneg hκ.le _
  refine ⟨C*(1+P),mul_nonneg hC (by positivity),?_⟩
  intro y t hy hyα hy1 ht htR hne
  let s : ℂ := (t : ℂ)+y*Complex.I
  have hs : 0 < s.im := by simpa [s] using hy
  have hre : 0 ≤ s.re := by simpa [s] using hδ.le.trans ht
  have hl : δ ≤ ‖s‖ := by
    have hh := Complex.re_le_norm s
    have he : s.re = t := by simp [s]
    rw [he] at hh
    exact ht.trans hh
  have hu : ‖s‖ ≤ R+1 := by
    have hh := norm_add_le (t : ℂ) ((y : ℂ)*Complex.I)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hδ.trans_le ht), abs_of_pos hy] at hh
    dsimp [s]
    linarith
  have ha := horizontalCritical_bounds hα hy.le hyα
  have hm := reciprocalMap_im_lower_horizontal hα hδ (by linarith : 0 < R+1) hy ht
    (show 0 ≤ horizontalCritical α y by unfold horizontalCritical; positivity) ha.2.2 hu
  have hx : 0 < |t-horizontalCritical α y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hmpos : 0 < |(reciprocalMap α s).im| := (mul_pos (mul_pos hκ hy) hx).trans_le hm
  have hsn : ‖s‖ ≠ α := by
    intro he
    have hi := (reciprocalMap_im_sign hs α).2.1.mpr he
    rw [hi, abs_zero] at hmpos
    exact lt_irrefl 0 hmpos
  have hw := hbound s hs (by simpa [s] using hy1) hre hl hu hsn
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos (mul_pos hκ hy) hx) hm
    (by norm_num : -(1/3 : ℝ) ≤ 0)
  have hmul := (mul_le_mul_of_nonneg_left hp hy.le).trans (weighted_inverse_third_bound hκ hy hy1 hx)
  have hpow : 0 ≤ ‖t-horizontalCritical α y‖^(-(1/3 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  rw [← Real.norm_eq_abs] at hmul
  change y*|(reciprocalMap α s).im|^(-(1/3 : ℝ)) ≤ P*‖t-horizontalCritical α y‖^(-(1/3 : ℝ)) at hmul
  have hCmul := mul_le_mul_of_nonneg_left hmul hC
  have hrest : 0 ≤ C*(P+‖t-horizontalCritical α y‖^(-(1/3 : ℝ))) := by positivity
  change |(momentTransform α s).im|+y*‖momentTransform α s‖ ≤ _
  have he : s.im = y := by simp [s]
  rw [he] at hw
  nlinarith

end AperyMoments
