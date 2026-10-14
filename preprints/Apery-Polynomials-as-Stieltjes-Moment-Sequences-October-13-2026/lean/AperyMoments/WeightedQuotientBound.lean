import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
namespace AperyMoments

theorem complex_quotient_im_bound (A q : ℂ) (hq : q ≠ 0) :
    |(A/q).im| ≤ |A.im|/‖q‖ + |q.im| *‖A‖/‖q‖^2 := by
  have hn := norm_pos_iff.mpr hq
  rw [Complex.div_im, ← sub_div, abs_div, abs_of_pos (Complex.normSq_pos.mpr hq), Complex.normSq_eq_norm_sq]
  have hh := abs_sub (A.im*q.re) (A.re*q.im)
  simp only [abs_mul] at hh
  have h₁ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm q) (abs_nonneg A.im)
  have h₂ := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm A) (abs_nonneg q.im)
  calc
    _ ≤ (|A.im| *‖q‖+‖A‖*|q.im|)/‖q‖^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith
    _ = _ := by field_simp

theorem weighted_quotient_bound {A E q : ℂ} {d K H y : ℝ}
    (hd : 0 < d) (hq : d ≤ ‖q‖) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hK : 0 ≤ K) (hA : |A.im| ≤ K) (hH : 0 ≤ H) (hE : ‖E‖ ≤ H)
    (hqi : |q.im| ≤ y/d) :
    |((A-E)/q).im|+y*‖(A-E)/q‖ ≤
      (K+2*H)/d + y*‖A‖*(1/d+1/d^3) := by
  have hqp : 0 < ‖q‖ := hd.trans_le hq
  have hqn : q ≠ 0 := norm_pos_iff.mp hqp
  have hAi := complex_quotient_im_bound A q hqn
  have hAi' : |(A/q).im| ≤ K/d + y*‖A‖/d^3 := by
    apply hAi.trans
    apply add_le_add
    · exact div_le_div₀ hK hA hd hq
    · have hsq : d^2 ≤ ‖q‖^2 := by nlinarith
      calc
        _ ≤ (y/d)*‖A‖/d^2 := by
          apply div_le_div₀ (mul_nonneg (div_nonneg hy hd.le) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hqi (norm_nonneg _)) (sq_pos_of_pos hd) hsq
        _ = _ := by ring
  have hEn : ‖E/q‖ ≤ H/d := by
    rw [norm_div]
    exact div_le_div₀ hH hE hd hq
  have hAn : ‖A/q‖ ≤ ‖A‖/d := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg A) hd hq
  have hI : |((A-E)/q).im| ≤ |(A/q).im|+‖E/q‖ := by
    rw [sub_div, Complex.sub_im]
    exact (abs_sub _ _).trans (add_le_add le_rfl (Complex.abs_im_le_norm _))
  have hN : ‖(A-E)/q‖ ≤ ‖A/q‖+‖E/q‖ := by rw [sub_div]; exact norm_sub_le _ _
  have hh := mul_le_mul_of_nonneg_left (hN.trans (add_le_add hAn hEn)) hy
  have he := mul_le_mul_of_nonneg_right hy1 (div_nonneg hH hd.le)
  have hEq : (K+2*H)/d+y*‖A‖*(1/d+1/d^3) = K/d+H/d+H/d+y*(‖A‖/d)+y*‖A‖/d^3 := by ring
  rw [hEq]
  linarith

end AperyMoments
