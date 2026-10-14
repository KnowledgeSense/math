import ArithmeticSections.QuadraticBounds

namespace ArithmeticSections

/-- A rational-polynomial lower bound obtained from the half-angle formula. -/
theorem cosine_lower_polynomial {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 2) :
    1 - x ^ 2 / 2 + x ^ 4 / 32 ≤ Real.cos x := by
  have h := Real.one_sub_sq_div_two_le_cos (x := x / 2)
  have hlo : 0 ≤ 1 - (x / 2) ^ 2 / 2 := by nlinarith
  have hsq := mul_self_le_mul_self hlo h
  have he := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at he
  nlinarith

/-- A rational-polynomial upper bound obtained from the sine cubic bound. -/
theorem cosine_upper_polynomial {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 2) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := Real.sin_ge_sub_cube (x := x / 2) (by linarith)
  have hc : 0 ≤ x / 2 - (x / 2) ^ 3 / 6 := by
    have h2 : (x / 2) ^ 2 ≤ 1 := by nlinarith
    have hh := mul_nonneg (show 0 ≤ x / 2 by linarith) (show 0 ≤ 1 - (x / 2) ^ 2 / 6 by linarith)
    nlinarith
  have hsq := mul_self_le_mul_self hc h
  have he := Real.cos_two_mul_eq_one_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at he
  nlinarith [sq_nonneg (x ^ 3)]

/-- An interval interface for checking the seed's finitely many cosine signs. -/
theorem cosine_rational_bounds {x lo hi : ℝ} (hl : 0 ≤ lo) (hh : hi ≤ 2)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    1 - hi ^ 2 / 2 + hi ^ 4 / 32 ≤ Real.cos x ∧
      Real.cos x ≤ 1 - lo ^ 2 / 2 + lo ^ 4 / 24 := by
  have hx : 0 ≤ x := hl.trans hlo
  constructor
  · exact (cosine_lower_polynomial (hx.trans hhi) hh).trans
      (Real.cos_le_cos_of_nonneg_of_le_pi hx (by linarith [Real.pi_gt_three]) hhi)
  · exact (Real.cos_le_cos_of_nonneg_of_le_pi hl (by linarith [Real.pi_gt_three]) hlo).trans
      (cosine_upper_polynomial hl (hlo.trans (hhi.trans hh)))

end ArithmeticSections
