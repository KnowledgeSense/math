import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Tactic

noncomputable section
namespace AperyMoments

/-- The reciprocal change of variable on the principal square-root branch. -/
def reciprocalMap (α : ℝ) (s : ℂ) : ℂ := Complex.sqrt s + (α:ℂ)/Complex.sqrt s

theorem sqrt_upper_parts {s : ℂ} (hs : 0 < s.im) :
    0 < (Complex.sqrt s).re ∧ 0 < (Complex.sqrt s).im ∧
      Complex.normSq (Complex.sqrt s)=‖s‖ := by
  have hb := abs_lt.mp (Complex.abs_re_lt_norm.mpr (ne_of_gt hs))
  have hp : 0 < (‖s‖+s.re)/2 := by linarith
  have hm : 0 < (‖s‖-s.re)/2 := by linarith
  have hr : (Complex.sqrt s).re=Real.sqrt ((‖s‖+s.re)/2) := by
    exact Complex.cpow_inv_two_re s
  have hi : (Complex.sqrt s).im=Real.sqrt ((‖s‖-s.re)/2) := by
    exact Complex.cpow_inv_two_im_eq_sqrt hs.le
  refine ⟨hr ▸ Real.sqrt_pos.mpr hp, hi ▸ Real.sqrt_pos.mpr hm, ?_⟩
  rw [Complex.normSq_apply, hr, hi]
  nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hm.le]

theorem sqrt_upper_norm {s : ℂ} (hs : 0 < s.im) : ‖Complex.sqrt s‖^2=‖s‖ := by
  rw [← Complex.normSq_eq_norm_sq]
  exact (sqrt_upper_parts hs).2.2

theorem reciprocalMap_re {s : ℂ} (hs : 0 < s.im) (α : ℝ) :
    (reciprocalMap α s).re=(Complex.sqrt s).re*(1+α/‖s‖) := by
  simp only [reciprocalMap, Complex.add_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, (sqrt_upper_parts hs).2.2]
  ring

theorem reciprocalMap_im {s : ℂ} (hs : 0 < s.im) (α : ℝ) :
    (reciprocalMap α s).im=(Complex.sqrt s).im*(1-α/‖s‖) := by
  simp only [reciprocalMap, Complex.add_im, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, (sqrt_upper_parts hs).2.2]
  ring

theorem reciprocalMap_re_pos {s : ℂ} (hs : 0 < s.im) {α : ℝ} (hα : 0 < α) :
    0 < (reciprocalMap α s).re := by
  rw [reciprocalMap_re hs]
  exact mul_pos (sqrt_upper_parts hs).1 (by positivity)

theorem reciprocalMap_im_sign {s : ℂ} (hs : 0 < s.im) (α : ℝ) :
    ((reciprocalMap α s).im < 0 ↔ ‖s‖ < α) ∧
    ((reciprocalMap α s).im = 0 ↔ ‖s‖ = α) ∧
    (0 < (reciprocalMap α s).im ↔ α < ‖s‖) := by
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr (by intro he; subst s; simp at hs)
  have hq := (sqrt_upper_parts hs).2.1
  rw [reciprocalMap_im hs]
  constructor
  · have he : (Complex.sqrt s).im*(1-α/‖s‖)<0 ↔ 1-α/‖s‖<0 := by
      constructor
      · intro h; nlinarith
      · exact mul_neg_of_pos_of_neg hq
    rw [he, sub_neg, one_lt_div hnorm]
  constructor
  · rw [mul_eq_zero, or_iff_right (ne_of_gt hq), sub_eq_zero, eq_div_iff (ne_of_gt hnorm)]
    simp
  · rw [mul_pos_iff_of_pos_left hq, sub_pos, div_lt_one hnorm]

theorem reciprocalMap_on_semicircle {s : ℂ} (hs : 0 < s.im) {α : ℝ}
    (hα : 0 < α) (hn : ‖s‖=α) :
    0 < (reciprocalMap α s).re ∧ (reciprocalMap α s).re < 2*Real.sqrt α ∧
      (reciprocalMap α s).im=0 := by
  have hp := sqrt_upper_parts hs
  have hnorm : (Complex.sqrt s).re^2+(Complex.sqrt s).im^2=α := by
    simpa only [Complex.normSq_apply, sq, hn] using hp.2.2
  have hlt : (Complex.sqrt s).re < Real.sqrt α := by
    have := Real.sq_sqrt hα.le
    have := Real.sqrt_nonneg α
    nlinarith [sq_pos_of_pos hp.2.1]
  refine ⟨reciprocalMap_re_pos hs hα, ?_, (reciprocalMap_im_sign hs α).2.1.mpr hn⟩
  rw [reciprocalMap_re hs, hn, div_self (ne_of_gt hα)]
  linarith

end AperyMoments
