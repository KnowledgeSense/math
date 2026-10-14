import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

theorem sinh_scale_bound {m x : ℝ} (hm : 1 ≤ m) (hx : 0 ≤ x) :
    m * Real.sinh x ≤ Real.sinh (m * x) := by
  let f : ℝ → ℝ := fun y => Real.sinh (m * y) - m * Real.sinh y
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hder (y : ℝ) :
      HasDerivAt f (m * (Real.cosh (m * y) - Real.cosh y)) y := by
    have h := ((Real.hasDerivAt_sinh (m * y)).comp y
      ((hasDerivAt_id y).const_mul m)).sub
        ((Real.hasDerivAt_sinh y).const_mul m)
    convert h using 1
    · rfl
    · ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · intro y _
      exact (hder y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hder y).deriv]
      have hy0 : 0 ≤ y := hy.le
      have hmy : 0 ≤ m * y := mul_nonneg hm0 hy0
      have hle : y ≤ m * y := by nlinarith
      have hc : Real.cosh y ≤ Real.cosh (m * y) :=
        Real.cosh_strictMonoOn.monotoneOn hy0 hmy hle
      exact mul_nonneg hm0 (sub_nonneg.mpr hc)
  have h := hmono (by simp) hx hx
  dsimp [f] at h
  simp only [mul_zero, Real.sinh_zero, mul_zero, sub_self] at h
  linarith

theorem sinh_ratio_bound {m x : ℝ} (hm : 1 ≤ m) (hx : x ≠ 0) :
    m ≤ Real.sinh (m * x) / Real.sinh x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hs := sinh_scale_bound hm (show 0 ≤ -x by linarith)
    simp only [mul_neg, Real.sinh_neg] at hs
    have hden : Real.sinh x < 0 := Real.sinh_neg_iff.mpr hneg
    apply (le_div_iff_of_neg hden).mpr
    linarith
  · have hs := sinh_scale_bound hm hpos.le
    have hden : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hpos
    exact (le_div_iff₀ hden).mpr hs

theorem sinh_scale_strict {m x : ℝ} (hm : 1 < m) (hx : 0 < x) :
    m * Real.sinh x < Real.sinh (m * x) := by
  let f : ℝ → ℝ := fun y => Real.sinh (m * y) - m * Real.sinh y
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have hder (y : ℝ) :
      HasDerivAt f (m * (Real.cosh (m * y) - Real.cosh y)) y := by
    have h := ((Real.hasDerivAt_sinh (m * y)).comp y
      ((hasDerivAt_id y).const_mul m)).sub
        ((Real.hasDerivAt_sinh y).const_mul m)
    convert h using 1
    · rfl
    · ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · fun_prop
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hder y).deriv]
      have hy0 : 0 < y := hy
      have hmy : 0 ≤ m * y := mul_nonneg hm0.le hy0.le
      have hlt : y < m * y := by nlinarith
      have hc : Real.cosh y < Real.cosh (m * y) :=
        Real.cosh_strictMonoOn hy0.le hmy hlt
      exact mul_pos hm0 (sub_pos.mpr hc)
  have h := hmono (by simp) hx.le hx
  dsimp [f] at h
  simp only [mul_zero, Real.sinh_zero, mul_zero, sub_self] at h
  linarith

theorem scaled_sinh_square_strict {a b s : ℝ} (ha : 0 < a) (hab : a < b)
    (hs : 0 < s) :
    b ^ 2 * Real.sinh (a * s) ^ 2 < a ^ 2 * Real.sinh (b * s) ^ 2 := by
  have hm : 1 < b / a := (lt_div_iff₀ ha).mpr (by linarith)
  have h := sinh_scale_strict hm (mul_pos ha hs)
  have hid : b / a * (a * s) = b * s := by field_simp [ha.ne']
  rw [hid] at h
  have hmul := (div_lt_iff₀ ha).mp
    (show b * Real.sinh (a * s) / a < Real.sinh (b * s) by convert h using 1; ring)
  have hleft : 0 < b * Real.sinh (a * s) :=
    mul_pos (lt_trans ha hab) (Real.sinh_pos_iff.mpr (mul_pos ha hs))
  have hright : 0 < a * Real.sinh (b * s) :=
    mul_pos ha (Real.sinh_pos_iff.mpr (mul_pos (lt_trans ha hab) hs))
  have hsq : (b * Real.sinh (a * s)) ^ 2 < (a * Real.sinh (b * s)) ^ 2 := by
    have hstrict : b * Real.sinh (a * s) < a * Real.sinh (b * s) := by simpa [mul_comm] using hmul
    have hd := mul_pos (sub_pos.mpr hstrict) (add_pos hleft hright)
    nlinarith
  simpa only [mul_pow] using hsq

end ResearchMain.DiagonalSchatten
