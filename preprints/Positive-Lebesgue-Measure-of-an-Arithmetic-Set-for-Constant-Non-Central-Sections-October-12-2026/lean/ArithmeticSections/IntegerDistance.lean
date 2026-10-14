import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Lipschitz

namespace ArithmeticSections

/-- Distance to the nearest integer. -/
noncomputable def integerDistance (x : ℝ) : ℝ := |x - (round x : ℝ)|

theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

theorem integerDistance_le_half (x : ℝ) : integerDistance x ≤ 1 / 2 := abs_sub_round x

theorem integerDistance_le_sub_integer (x : ℝ) (m : ℤ) :
    integerDistance x ≤ |x - (m : ℝ)| := round_le x m

theorem integerDistance_double (x : ℝ) : integerDistance (2 * x) ≤ 2 * integerDistance x := by
  calc
    integerDistance (2 * x) ≤ |2 * x - ((2 * round x : ℤ) : ℝ)| := integerDistance_le_sub_integer _ _
    _ = 2 * integerDistance x := by
      simp only [Int.cast_mul, Int.cast_ofNat, integerDistance]
      rw [← mul_sub, abs_mul]
      norm_num

theorem integerDistance_lipschitz (x y : ℝ) :
    |integerDistance x - integerDistance y| ≤ |x - y| := by
  have hxy : integerDistance x ≤ |x - y| + integerDistance y := by
    calc
      integerDistance x ≤ |x - (round y : ℝ)| := integerDistance_le_sub_integer _ _
      _ = |(x - y) + (y - (round y : ℝ))| := by congr 1; ring
      _ ≤ |x - y| + integerDistance y := abs_add_le _ _
  have hyx : integerDistance y ≤ |x - y| + integerDistance x := by
    calc
      integerDistance y ≤ |y - (round x : ℝ)| := integerDistance_le_sub_integer _ _
      _ = |(y - x) + (x - (round x : ℝ))| := by congr 1; ring
      _ ≤ |y - x| + integerDistance x := abs_add_le _ _
      _ = |x - y| + integerDistance x := by rw [abs_sub_comm y x]
  rw [abs_le]
  constructor <;> linarith

/-- Continuity used in Lemma 2.4. -/
theorem continuous_integerDistance : Continuous integerDistance := by
  have h : LipschitzWith 1 integerDistance := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using integerDistance_lipschitz x y)
  exact h.continuous

theorem integerDistance_pos {x : ℝ} (hx : Irrational x) : 0 < integerDistance x := by
  apply abs_pos.mpr
  exact sub_ne_zero.mpr (hx.ne_int (round x))

theorem integerDistance_lt_half {x : ℝ} (hx : Irrational x) : integerDistance x < 1 / 2 := by
  apply lt_of_le_of_ne (integerDistance_le_half x)
  intro h
  have he : |x - (round x : ℝ)| = |(1 / 2 : ℝ)| := by simpa [integerDistance] using h
  rcases abs_eq_abs.mp he with he | he
  · exact (hx.sub_intCast (round x)).ne_rat (1 / 2) (by norm_num; exact he)
  · exact (hx.sub_intCast (round x)).ne_rat (-1 / 2) (by norm_num; linarith)

theorem integerDistance_mul_ne {x : ℝ} (hx : Irrational x)
    {m n : ℤ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    integerDistance (m * x) ≠ integerDistance (n * x) := by
  intro h
  rcases abs_eq_abs.mp h with h | h
  · have hi := hx.mul_intCast (sub_ne_zero.mpr hmn)
    apply hi.ne_int (round (m * x) - round (n * x))
    push_cast
    nlinarith
  · have hi := hx.mul_intCast (show m + n ≠ 0 by omega)
    apply hi.ne_int (round (m * x) + round (n * x))
    push_cast
    nlinarith

end ArithmeticSections
