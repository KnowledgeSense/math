import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

def quadratic (a b c x : ℝ) : ℝ := a * x ^ 2 + b * x + c

theorem quadratic_chord_identity (a b c l r x : ℝ) :
    (r - l) * quadratic a b c x -
      (r - x) * quadratic a b c l - (x - l) * quadratic a b c r =
      -a * (r - l) * (x - l) * (r - x) := by
  unfold quadratic
  ring

theorem quadratic_positive_on_interval (a b c l r x : ℝ)
    (ha : a ≤ 0) (hlr : l < r) (hlx : l ≤ x) (hxr : x ≤ r)
    (hl : 0 < quadratic a b c l) (hr : 0 < quadratic a b c r) :
    0 < quadratic a b c x := by
  have hgap : 0 < r - l := sub_pos.mpr hlr
  have hleft : 0 ≤ x - l := sub_nonneg.mpr hlx
  have hright : 0 ≤ r - x := sub_nonneg.mpr hxr
  have herror : 0 ≤ -a * (r - l) * (x - l) * (r - x) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (neg_nonneg.mpr ha) hgap.le) hleft)
      hright
  have hsum : 0 < (r - x) * quadratic a b c l +
      (x - l) * quadratic a b c r := by
    by_cases hzero : x = l
    · subst x
      simpa using mul_pos hgap hl
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hright hl.le)
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne hlx (Ne.symm hzero))) hr)
  have hidentity := quadratic_chord_identity a b c l r x
  have hscaled : 0 < (r - l) * quadratic a b c x := by linarith
  exact pos_of_mul_pos_right hscaled hgap.le

theorem quadratic_positive_on_open_interval (a b c l r x : ℝ)
    (ha : a < 0) (hlr : l < r) (hlx : l < x) (hxr : x < r)
    (hl : 0 ≤ quadratic a b c l) (hr : 0 ≤ quadratic a b c r) :
    0 < quadratic a b c x := by
  have hgap : 0 < r - l := sub_pos.mpr hlr
  have hleft : 0 < x - l := sub_pos.mpr hlx
  have hright : 0 < r - x := sub_pos.mpr hxr
  have herror : 0 < -a * (r - l) * (x - l) * (r - x) := by
    exact mul_pos (mul_pos (mul_pos (neg_pos.mpr ha) hgap) hleft) hright
  have hsum : 0 ≤ (r - x) * quadratic a b c l +
      (x - l) * quadratic a b c r :=
    add_nonneg (mul_nonneg hright.le hl) (mul_nonneg hleft.le hr)
  have hidentity := quadratic_chord_identity a b c l r x
  have hscaled : 0 < (r - l) * quadratic a b c x := by linarith
  exact pos_of_mul_pos_right hscaled hgap.le

end ResearchMain.DiagonalSchatten
