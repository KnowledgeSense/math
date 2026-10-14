import MainTheorems.DominationRoots.Taylor

namespace ResearchMain.DominationRoots

open Set

def quadratic (c d x : ℝ) : ℝ := x ^ 2 - c * x + d

theorem quadratic_increasing {c d a b x : ℝ} (ha : c ≤ 2 * a)
    (hx : x ∈ Icc a b) :
    quadratic c d a ≤ quadratic c d x ∧ quadratic c d x ≤ quadratic c d b := by
  rcases hx with ⟨hax, hxb⟩
  unfold quadratic
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hax) (show 0 ≤ x + a - c by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxb) (show 0 ≤ b + x - c by linarith)]

theorem quadratic_decreasing {c d a b x : ℝ} (hb : 2 * b ≤ c)
    (hx : x ∈ Icc a b) :
    quadratic c d b ≤ quadratic c d x ∧ quadratic c d x ≤ quadratic c d a := by
  rcases hx with ⟨hax, hxb⟩
  unfold quadratic
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxb) (show 0 ≤ c - b - x by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hax) (show 0 ≤ c - x - a by linarith)]

theorem abs_le_max_of_between {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    |x| ≤ max |a| |b| := by
  apply abs_le.mpr
  constructor
  · have h := neg_abs_le a
    have hm := le_max_left |a| |b|
    linarith
  · exact hx.2.trans ((le_abs_self b).trans (le_max_right _ _))

theorem abs_sub_le_max {a b c x : ℝ} (hx : x ∈ Icc a b) :
    |x - c| ≤ max |a - c| |b - c| :=
  abs_le_max_of_between ⟨sub_le_sub_right hx.1 c, sub_le_sub_right hx.2 c⟩

theorem quadratic_abs_bound {c d a b x : ℝ}
    (hs : c ≤ 2 * a ∨ 2 * b ≤ c) (hx : x ∈ Icc a b) :
    |quadratic c d x| ≤ max |quadratic c d a| |quadratic c d b| := by
  rcases hs with hs | hs
  · exact abs_le_max_of_between (quadratic_increasing hs hx)
  · simpa [max_comm] using abs_le_max_of_between (quadratic_decreasing hs hx)

def auxiliaryQ (x : ℝ) : ℝ := x * (x - 1) ^ 2 * (x - 2) * quadratic 3 1 x

def bracketBound (a b : ℝ) : ℝ :=
  b * (max |a - 1| |b - 1|) ^ 2 * max |a - 2| |b - 2| *
    max |quadratic 3 1 a| |quadratic 3 1 b|

theorem auxiliaryQ_bracket_bound {a b x : ℝ} (ha : 0 ≤ a)
    (hs : 3 ≤ 2 * a ∨ 2 * b ≤ 3) (hx : x ∈ Icc a b) :
    |auxiliaryQ x| ≤ bracketBound a b := by
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hb0 : 0 ≤ b := hx0.trans hx.2
  have h1 := abs_sub_le_max (c := 1) hx
  have h2 := abs_sub_le_max (c := 2) hx
  have hq := quadratic_abs_bound hs hx (d := 1)
  have hsq : |x - 1| ^ 2 ≤ (max |a - 1| |b - 1|) ^ 2 := by
    nlinarith [abs_nonneg (x - 1), le_max_left |a - 1| |b - 1|]
  unfold auxiliaryQ bracketBound
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hx0]
  apply mul_le_mul ?_ hq (by positivity) (by positivity)
  apply mul_le_mul ?_ h2 (by positivity) (by positivity)
  exact mul_le_mul hx.2 hsq (by positivity) hb0

theorem energy_bracket_bound {a b x : ℝ}
    (hs : 1 ≤ 2 * a ∨ 2 * b ≤ 1) (hx : x ∈ Icc a b) :
    min (quadratic 1 (-2) a) (quadratic 1 (-2) b) ≤ quadratic 1 (-2) x := by
  rcases hs with hs | hs
  · exact (min_le_left _ _).trans (quadratic_increasing hs hx).1
  · exact (min_le_right _ _).trans (quadratic_decreasing hs hx).1

end ResearchMain.DominationRoots
