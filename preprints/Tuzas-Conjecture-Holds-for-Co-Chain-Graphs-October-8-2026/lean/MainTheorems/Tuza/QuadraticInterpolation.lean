import Mathlib.Tactic

namespace ResearchMain.Tuza

theorem concave_quadratic_lower (α β γ L l u x : ℝ) (hγ : 0 ≤ γ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : L ≤ α + β * l - γ * l ^ 2)
    (hu : L ≤ α + β * u - γ * u ^ 2) :
    L ≤ α + β * x - γ * x ^ 2 := by
  by_cases hlu : l = u
  · have hxl : x = l := by linarith
    simpa only [hxl] using hl
  · have hpos : 0 < u - l := sub_pos.mpr (lt_of_le_of_ne (hlx.trans hxu) hlu)
    have he : (u - l) * (α + β * x - γ * x ^ 2 - L) =
        (u - x) * (α + β * l - γ * l ^ 2 - L) +
        (x - l) * (α + β * u - γ * u ^ 2 - L) +
        γ * (u - l) * (x - l) * (u - x) := by ring
    have hn : 0 ≤ (u - l) * (α + β * x - γ * x ^ 2 - L) := by
      rw [he]
      exact add_nonneg (add_nonneg (mul_nonneg (by linarith) (by linarith))
        (mul_nonneg (by linarith) (by linarith))) (by positivity)
    have := (mul_nonneg_iff_of_pos_left hpos).mp hn
    linarith

end ResearchMain.Tuza
