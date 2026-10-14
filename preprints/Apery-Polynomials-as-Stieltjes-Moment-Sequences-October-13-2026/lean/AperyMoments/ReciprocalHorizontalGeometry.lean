import AperyMoments.ReciprocalMap

noncomputable section
namespace AperyMoments

theorem sqrt_upper_product {s : ℂ} (hs : 0 < s.im) :
    2*(Complex.sqrt s).re*(Complex.sqrt s).im = s.im := by
  have hp := sqrt_upper_parts hs
  have hr : (Complex.sqrt s).re^2 = (‖s‖+s.re)/2 := by
    have he : (Complex.sqrt s).re = Real.sqrt ((‖s‖+s.re)/2) := Complex.cpow_inv_two_re s
    rw [he, Real.sq_sqrt]
    linarith [Complex.abs_re_le_norm s, neg_le_abs s.re]
  have hi : (Complex.sqrt s).im^2 = (‖s‖-s.re)/2 := by
    have he : (Complex.sqrt s).im = Real.sqrt ((‖s‖-s.re)/2) := Complex.cpow_inv_two_im_eq_sqrt hs.le
    rw [he, Real.sq_sqrt]
    linarith [Complex.re_le_norm s]
  have hn : ‖s‖^2 = s.re^2+s.im^2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have he : (2*(Complex.sqrt s).re*(Complex.sqrt s).im)^2 = s.im^2 := by
    rw [mul_pow, mul_pow, hr, hi]
    nlinarith
  nlinarith [mul_pos hp.1 hp.2.1]

theorem reciprocalMap_re_lower_positive {α : ℝ} (hα : 0 ≤ α) {s : ℂ}
    (hs : 0 < s.im) (hre : 0 ≤ s.re) : Real.sqrt α ≤ (reciprocalMap α s).re := by
  have hp := sqrt_upper_parts hs
  have hq : 0 < ‖Complex.sqrt s‖ := (lt_of_lt_of_le hp.1 (Complex.re_le_norm _))
  have hn := sqrt_upper_norm hs
  have hr : (Complex.sqrt s).re^2 = (‖s‖+s.re)/2 := by
    have he : (Complex.sqrt s).re = Real.sqrt ((‖s‖+s.re)/2) := Complex.cpow_inv_two_re s
    rw [he, Real.sq_sqrt]
    positivity
  have hqr : ‖Complex.sqrt s‖/2 ≤ (Complex.sqrt s).re := by nlinarith
  have hs0 : 0 < ‖s‖ := by nlinarith
  have ha := Real.sqrt_nonneg α
  have ha2 := Real.sq_sqrt hα
  have hsum : 2*‖Complex.sqrt s‖*Real.sqrt α ≤ ‖s‖+α := by
    nlinarith [sq_nonneg (‖Complex.sqrt s‖-Real.sqrt α)]
  have hm := mul_le_mul_of_nonneg_right hqr (show 0 ≤ ‖s‖+α by positivity)
  have hm' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ ‖Complex.sqrt s‖/2 by positivity)
  rw [reciprocalMap_re hs]
  have he : (Complex.sqrt s).re*(1+α/‖s‖) =
      ((Complex.sqrt s).re*(‖s‖+α))/‖s‖ := by field_simp
  rw [he, le_div_iff₀ hs0]
  nlinarith

def horizontalCritical (α y : ℝ) : ℝ := Real.sqrt (α^2-y^2)

theorem horizontalCritical_bounds {α y : ℝ} (hα : 0 < α) (hy : 0 ≤ y) (hyα : y ≤ α/2) :
    α/2 ≤ horizontalCritical α y ∧ horizontalCritical α y ≤ α ∧
      (horizontalCritical α y)^2+y^2=α^2 := by
  have hbase : 0 ≤ α^2-y^2 := by nlinarith
  have hs := Real.sq_sqrt hbase
  have hn := Real.sqrt_nonneg (α^2-y^2)
  unfold horizontalCritical
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem horizontal_norm_difference {α y t a : ℝ} (_hα : 0 < α)
    (ha : a^2+y^2=α^2) :
    (‖(t : ℂ)+y*Complex.I‖-α)*(‖(t : ℂ)+y*Complex.I‖+α) = (t-a)*(t+a) := by
  have hn : ‖(t : ℂ)+y*Complex.I‖^2=t^2+y^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  nlinarith

theorem reciprocalMap_im_abs_horizontal {α y t a : ℝ} (hα : 0 < α) (hy : 0 < y)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (ha2 : a^2+y^2=α^2) :
    |(reciprocalMap α ((t : ℂ)+y*Complex.I)).im| =
      y*|t-a| *(t+a)/(2*(Complex.sqrt ((t : ℂ)+y*Complex.I)).re*
        ‖(t : ℂ)+y*Complex.I‖*(‖(t : ℂ)+y*Complex.I‖+α)) := by
  let s : ℂ := (t : ℂ)+y*Complex.I
  have hs : 0 < s.im := by simpa [s] using hy
  have hp := sqrt_upper_parts hs
  have hqr : 0 < (Complex.sqrt s).re := hp.1
  have hn : 0 < ‖s‖ := (lt_of_lt_of_le hs (Complex.im_le_norm s))
  have hnp : 0 < ‖s‖+α := by positivity
  have hprod := sqrt_upper_product hs
  have hdelta : |‖s‖-α| *(‖s‖+α) = |t-a| *(t+a) := by
    have hh := congrArg abs (horizontal_norm_difference (t := t) hα ha2)
    change |(‖s‖-α)*(‖s‖+α)| = |(t-a)*(t+a)| at hh
    simpa only [abs_mul, abs_of_pos hnp, abs_of_nonneg (add_nonneg ht ha)] using hh
  have hqi : (Complex.sqrt s).im = y/(2*(Complex.sqrt s).re) := by
    apply (eq_div_iff (by positivity : 2*(Complex.sqrt s).re ≠ 0)).mpr
    have he : s.im = y := by simp [s]
    rw [he] at hprod
    nlinarith
  change |(reciprocalMap α s).im| = _
  rw [reciprocalMap_im hs, abs_mul, abs_of_pos hp.2.1, hqi]
  have he : 1-α/‖s‖ = (‖s‖-α)/‖s‖ := by field_simp
  rw [he, abs_div, abs_of_pos hn]
  change y/(2*(Complex.sqrt s).re)*(|‖s‖-α|/‖s‖) =
    y*|t-a| *(t+a)/(2*(Complex.sqrt s).re*‖s‖*(‖s‖+α))
  apply (eq_div_iff (by positivity : 2*(Complex.sqrt s).re*‖s‖*(‖s‖+α) ≠ 0)).mpr
  field_simp [hqr.ne', hn.ne']
  nlinarith [congrArg (fun r : ℝ => y*r) hdelta]

def horizontalCriticalConstant (α δ N : ℝ) : ℝ :=
  δ/(2*Real.sqrt N*N*(N+α))

theorem horizontalCriticalConstant_pos {α δ N : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hN : 0 < N) :
    0 < horizontalCriticalConstant α δ N := by
  unfold horizontalCriticalConstant
  positivity

theorem reciprocalMap_im_lower_horizontal {α δ N y t a : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hN : 0 < N) (hy : 0 < y)
    (ht : δ ≤ t) (ha : 0 ≤ a) (ha2 : a^2+y^2=α^2)
    (hbound : ‖(t : ℂ)+y*Complex.I‖ ≤ N) :
    horizontalCriticalConstant α δ N*y*|t-a| ≤ |(reciprocalMap α ((t : ℂ)+y*Complex.I)).im| := by
  let s : ℂ := (t : ℂ)+y*Complex.I
  have hs : 0 < s.im := by simpa [s] using hy
  have hqr := (sqrt_upper_parts hs).1
  have hn : 0 < ‖s‖ := hs.trans_le (Complex.im_le_norm s)
  have hq : (Complex.sqrt s).re ≤ Real.sqrt N := by
    have hsq := sqrt_upper_norm hs
    have hr := Complex.re_le_norm (Complex.sqrt s)
    have hroot := Real.sq_sqrt hN.le
    have hp := Real.sqrt_nonneg N
    nlinarith [norm_nonneg (Complex.sqrt s)]
  have hden : 2*(Complex.sqrt s).re*‖s‖*(‖s‖+α) ≤ 2*Real.sqrt N*N*(N+α) := by
    gcongr
  have hden0 : 0 < 2*(Complex.sqrt s).re*‖s‖*(‖s‖+α) := by positivity
  rw [reciprocalMap_im_abs_horizontal hα hy (hδ.le.trans ht) ha ha2]
  change horizontalCriticalConstant α δ N*y*|t-a| ≤
    y*|t-a| *(t+a)/(2*(Complex.sqrt s).re*‖s‖*(‖s‖+α))
  calc
    _ = y*|t-a| *δ/(2*Real.sqrt N*N*(N+α)) := by unfold horizontalCriticalConstant; ring
    _ ≤ y*|t-a| *(t+a)/(2*Real.sqrt N*N*(N+α)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith : δ ≤ t+a) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hy.le (abs_nonneg _)) (add_nonneg (hδ.le.trans ht) ha)) hden0 hden

theorem reciprocalMap_norm_bound {α δ N : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) {s : ℂ}
    (hs : 0 < s.im) (hl : δ ≤ ‖s‖) (hu : ‖s‖ ≤ N) :
    ‖reciprocalMap α s‖ ≤ Real.sqrt N+α/Real.sqrt δ := by
  have hq := sqrt_upper_norm hs
  have hN : 0 < N := hδ.trans_le (hl.trans hu)
  have hlow : Real.sqrt δ ≤ ‖Complex.sqrt s‖ := by
    have hp := Real.sqrt_nonneg δ
    have hn := norm_nonneg (Complex.sqrt s)
    nlinarith [Real.sq_sqrt hδ.le]
  have hhigh : ‖Complex.sqrt s‖ ≤ Real.sqrt N := by
    have hp := Real.sqrt_nonneg N
    have hn := norm_nonneg (Complex.sqrt s)
    nlinarith [Real.sq_sqrt hN.le]
  unfold reciprocalMap
  calc
    _ ≤ ‖Complex.sqrt s‖+‖(α : ℂ)/Complex.sqrt s‖ := norm_add_le _ _
    _ = ‖Complex.sqrt s‖+α/‖Complex.sqrt s‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ _ := add_le_add hhigh (div_le_div_of_nonneg_left hα (Real.sqrt_pos.mpr hδ) hlow)

theorem sqrt_upper_re_lower {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 0 < s.im) (hre : 0 ≤ s.re) (hl : δ ≤ ‖s‖) :
    Real.sqrt δ/2 ≤ (Complex.sqrt s).re := by
  have hp := (sqrt_upper_parts hs).1
  have hr : (Complex.sqrt s).re^2 = (‖s‖+s.re)/2 := by
    have he : (Complex.sqrt s).re = Real.sqrt ((‖s‖+s.re)/2) := Complex.cpow_inv_two_re s
    rw [he, Real.sq_sqrt]
    positivity
  have hn := Real.sqrt_nonneg δ
  nlinarith [Real.sq_sqrt hδ.le]

theorem sqrt_upper_im_bound {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 0 < s.im) (hre : 0 ≤ s.re) (hl : δ ≤ ‖s‖) :
    |(Complex.sqrt s).im| ≤ s.im/Real.sqrt δ := by
  have hp := sqrt_upper_parts hs
  rw [abs_of_pos hp.2.1, le_div_iff₀ (Real.sqrt_pos.mpr hδ)]
  have hr := sqrt_upper_re_lower hδ hs hre hl
  have he := sqrt_upper_product hs
  nlinarith [mul_le_mul_of_nonneg_right hr hp.2.1.le]

theorem sqrt_upper_norm_lower {δ : ℝ} (hδ : 0 < δ) {s : ℂ}
    (hs : 0 < s.im) (hl : δ ≤ ‖s‖) : Real.sqrt δ ≤ ‖Complex.sqrt s‖ := by
  have hn := norm_nonneg (Complex.sqrt s)
  have hr := Real.sqrt_nonneg δ
  nlinarith [Real.sq_sqrt hδ.le, sqrt_upper_norm hs]

end AperyMoments
