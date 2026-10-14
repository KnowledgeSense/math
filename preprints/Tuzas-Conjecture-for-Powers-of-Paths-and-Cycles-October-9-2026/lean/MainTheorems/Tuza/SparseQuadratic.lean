import MainTheorems.Tuza.QuadraticInterpolation

namespace ResearchMain.Tuza

theorem sparse_concave_bound (r t x : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxu : x ≤ r / 2) (hxl : r - t ≤ x) :
    (r ^ 2 + t ^ 2) / 2 ≤ t ^ 2 - t * x - 2 * x ^ 2 + 3 * r * x := by
  have hu : (r ^ 2 + t ^ 2) / 2 ≤
      t ^ 2 + (3 * r - t) * (r / 2) - 2 * (r / 2) ^ 2 := by
    nlinarith [sq_nonneg (r - t)]
  by_cases hrt : r ≤ t
  · have hl : (r ^ 2 + t ^ 2) / 2 ≤ t ^ 2 + (3 * r - t) * 0 - 2 * 0 ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ t - r) (by linarith : 0 ≤ t + r)]
    have h := concave_quadratic_lower (t ^ 2) (3 * r - t) 2
      ((r ^ 2 + t ^ 2) / 2) 0 (r / 2) x (by norm_num) hx hxu hl hu
    nlinarith
  · have hl : (r ^ 2 + t ^ 2) / 2 ≤
        t ^ 2 + (3 * r - t) * (r - t) - 2 * (r - t) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ r - t) (by linarith : 0 ≤ r + t)]
    have h := concave_quadratic_lower (t ^ 2) (3 * r - t) 2
      ((r ^ 2 + t ^ 2) / 2) (r - t) (r / 2) x (by norm_num) hxl hxu hl hu
    nlinarith

def sparseMargin (r t x y : ℝ) : ℝ :=
  (t + x) * (t + x - 2) - 3 + 3 * (r - x - 1) * min (x + y) (r - x) -
    3 * t * x - 3 * r * y + 3 * x * y - 3 * (r + t - 2)

theorem sparse_margin_bound (r t x y : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxr : x ≤ r) (horder : r + y ≤ t + x) :
    3 / 14 * (r ^ 2 + t ^ 2) - 6 * (r + t) + 83 / 28 ≤ sparseMargin r t x y := by
  by_cases hs : x + y ≤ r - x
  · have hxu : x ≤ r / 2 := by linarith
    have hxl : r - t ≤ x := by linarith
    have hq := sparse_concave_bound r t x hr ht hx hxu hxl
    have hsmall : 5 * x + 3 * y ≤ 3 * r := by linarith
    unfold sparseMargin
    rw [min_eq_left hs]
    nlinarith [sq_nonneg r, sq_nonneg t]
  · have hprod : 0 ≤ (r - x) * (t + x - r - y) :=
      mul_nonneg (by linarith) (by linarith)
    unfold sparseMargin
    rw [min_eq_right (le_of_not_ge hs)]
    nlinarith [sq_nonneg (14 * x - 12 * r + 2 * t + 1), sq_nonneg (r - t)]

theorem sparse_margin_positive (r t x y : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxr : x ≤ r) (horder : r + y ≤ t + x)
    (hlarge : 84 * (r + t) ≤ 3 * (r ^ 2 + t ^ 2)) :
    0 < sparseMargin r t x y := by
  have h := sparse_margin_bound r t x y hr ht hx hy hxr horder
  linarith

theorem sparse_margin_large_order (r t x y : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxr : x ≤ r) (horder : r + y ≤ t + x)
    (hlarge : 56 ≤ r + t) : 0 < sparseMargin r t x y := by
  apply sparse_margin_positive r t x y hr ht hx hy hxr horder
  nlinarith [sq_nonneg (r - t)]

end ResearchMain.Tuza
