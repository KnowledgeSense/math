import Mathlib.Tactic

namespace ResearchMain.Tuza

def denseMarginD (r t w z e : ℝ) : ℝ :=
  t * min (r + w) t + r * min z r - r * t - e

noncomputable def denseMarginF (r t w z e : ℝ) : ℝ :=
  (r + t + w + z) ^ 2 / 3 + (r - w) ^ 2 + (t - z) ^ 2 -
    r ^ 2 - t ^ 2 - r * t - 2 * w * z + e

noncomputable def denseMarginL (r t e : ℝ) : ℝ := (r ^ 2 + t ^ 2) / 3 - r * t - e

noncomputable def denseQuadratic (r t w z e : ℝ) : ℝ :=
  denseMarginF r t w z e + 3 / 4 * denseMarginD r t w z e + 1 / 4 * denseMarginL r t e

theorem dense_quadratic_00 (r t w z e : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hw : 0 ≤ w) (hz : 0 ≤ z) (hwt : r + w ≤ t) (hzr : z ≤ r) :
    (r + t) ^ 2 / 16 ≤ denseQuadratic r t w z e := by
  have he : denseQuadratic r t w z e - (r + t) ^ 2 / 16 =
      4 / 3 * (z - (t - r + w) / 2) ^ 2 + (t - r) ^ 2 / 48 +
      r * w / 12 + 3 * (t - r) * w / 4 + w ^ 2 + r * z / 12 := by
    unfold denseQuadratic denseMarginD denseMarginF denseMarginL
    rw [min_eq_left hwt, min_eq_left hzr]
    ring
  have hn : 0 ≤ 4 / 3 * (z - (t - r + w) / 2) ^ 2 + (t - r) ^ 2 / 48 +
      r * w / 12 + 3 * (t - r) * w / 4 + w ^ 2 + r * z / 12 := by
    have : 0 ≤ t - r := sub_nonneg.mpr hrt
    positivity
  linarith

noncomputable def positiveQuadratic01 (A B C : ℝ) : ℝ :=
  13 / 6 * (A - 33 / 52 * B + 6 / 13 * C) ^ 2 +
    575 / 1248 * (B - 8 / 115 * C) ^ 2 + 20 / 23 * C ^ 2

noncomputable def positiveQuadratic10 (A B C : ℝ) : ℝ :=
  35 / 12 * (A - 12 / 35 * B + 33 / 70 * C) ^ 2 +
    104 / 105 * (B - 41 / 208 * C) ^ 2 + 269 / 416 * C ^ 2

noncomputable def positiveQuadratic11 (A B C : ℝ) : ℝ :=
  11 / 3 * (A - 3 / 11 * B + 3 / 11 * C) ^ 2 +
    35 / 33 * (B - 13 / 35 * C) ^ 2 + 32 / 35 * C ^ 2

theorem positiveQuadratic01_nonneg (A B C : ℝ) : 0 ≤ positiveQuadratic01 A B C := by
  unfold positiveQuadratic01
  positivity

theorem positiveQuadratic10_nonneg (A B C : ℝ) : 0 ≤ positiveQuadratic10 A B C := by
  unfold positiveQuadratic10
  positivity

theorem positiveQuadratic11_nonneg (A B C : ℝ) : 0 ≤ positiveQuadratic11 A B C := by
  unfold positiveQuadratic11
  positivity

theorem dense_quadratic_01 (r t w z e : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hw : 0 ≤ w) (hwt : r + w ≤ t) (hrz : r ≤ z) :
    43 / 816 * (r + t) ^ 2 ≤ denseQuadratic r t w z e := by
  have he : denseQuadratic r t w z e = 43 / 816 * (r + t) ^ 2 +
      67 / 136 * (r + t) * w +
      positiveQuadratic01 (r - 5 / 34 * (r + t)) w (z - 53 / 136 * (r + t)) := by
    unfold denseQuadratic denseMarginD denseMarginF denseMarginL positiveQuadratic01
    rw [min_eq_left hwt, min_eq_right hrz]
    ring
  have hq := positiveQuadratic01_nonneg (r - 5 / 34 * (r + t)) w (z - 53 / 136 * (r + t))
  have hl : 0 ≤ 67 / 136 * (r + t) * w := by positivity
  linarith

theorem dense_quadratic_10 (r t w z e : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t)
    (htw : t ≤ r + w) (hzr : z ≤ r) :
    29 / 768 * (r + t) ^ 2 ≤ denseQuadratic r t w z e := by
  have he : denseQuadratic r t w z e = 29 / 768 * (r + t) ^ 2 +
      57 / 64 * (r + t) * ((r + t) / 2 - r) +
      positiveQuadratic10 (r - (r + t) / 2)
        (w - 5 / 32 * (r + t)) (z - (r + t) / 16) := by
    unfold denseQuadratic denseMarginD denseMarginF denseMarginL positiveQuadratic10
    rw [min_eq_right htw, min_eq_left hzr]
    ring
  have hq := positiveQuadratic10_nonneg (r - (r + t) / 2)
    (w - 5 / 32 * (r + t)) (z - (r + t) / 16)
  have hl : 0 ≤ 57 / 64 * (r + t) * ((r + t) / 2 - r) := by
    have : 0 ≤ r + t := by linarith
    have : 0 ≤ (r + t) / 2 - r := by linarith
    positivity
  linarith

theorem dense_quadratic_11 (r t w z e : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (htw : t ≤ r + w) (hrz : r ≤ z) :
    71 / 354 * (r + t) ^ 2 ≤ denseQuadratic r t w z e := by
  have he : denseQuadratic r t w z e = 71 / 354 * (r + t) ^ 2 +
      16 / 59 * (r + t) * (z - r) +
      positiveQuadratic11 (r - 25 / 59 * (r + t))
        (w - 33 / 118 * (r + t)) (z - 25 / 59 * (r + t)) := by
    unfold denseQuadratic denseMarginD denseMarginF denseMarginL positiveQuadratic11
    rw [min_eq_right htw, min_eq_right hrz]
    ring
  have hq := positiveQuadratic11_nonneg (r - 25 / 59 * (r + t))
    (w - 33 / 118 * (r + t)) (z - 25 / 59 * (r + t))
  have hl : 0 ≤ 16 / 59 * (r + t) * (z - r) := by
    have : 0 ≤ z - r := sub_nonneg.mpr hrz
    positivity
  linarith

theorem dense_quadratic_lower (r t w z e : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hw : 0 ≤ w) (hz : 0 ≤ z) :
    29 / 768 * (r + t) ^ 2 ≤ denseQuadratic r t w z e := by
  by_cases hwt : r + w ≤ t
  · by_cases hzr : z ≤ r
    · have h := dense_quadratic_00 r t w z e hr hrt hw hz hwt hzr
      nlinarith [sq_nonneg (r + t)]
    · have h := dense_quadratic_01 r t w z e hr (hr.trans hrt) hw hwt (le_of_not_ge hzr)
      nlinarith [sq_nonneg (r + t)]
  · by_cases hzr : z ≤ r
    · exact dense_quadratic_10 r t w z e hr hrt (le_of_not_ge hwt) hzr
    · have h := dense_quadratic_11 r t w z e hr (hr.trans hrt)
        (le_of_not_ge hwt) (le_of_not_ge hzr)
      nlinarith [sq_nonneg (r + t)]

theorem dense_integer_margins_positive (r t w z e d f l : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t)
    (hw : 0 ≤ w) (hz : 0 ≤ z) (hN : 88 ≤ r + t)
    (hd : denseMarginD r t w z e - 2 * (r + t) + 2 ≤ d)
    (hf : denseMarginF r t w z e - 5 / 3 * (r + t) + 1 ≤ f)
    (hl : denseMarginL r t e - 2 / 3 * (r + t) - 2 ≤ l) :
    0 < f + 3 / 4 * d + 1 / 4 * l := by
  have hq := dense_quadratic_lower r t w z e hr hrt hw hz
  unfold denseQuadratic at hq
  have hpoly : 0 < 29 / 768 * (r + t) ^ 2 - 10 / 3 * (r + t) + 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ r + t - 88) (by linarith : 0 ≤ r + t)]
  linarith

end ResearchMain.Tuza
