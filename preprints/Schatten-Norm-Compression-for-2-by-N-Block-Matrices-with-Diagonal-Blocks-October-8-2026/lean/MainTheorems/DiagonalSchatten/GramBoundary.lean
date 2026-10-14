import MainTheorems.DiagonalSchatten.Quadratic

namespace ResearchMain.DiagonalSchatten

noncomputable section

structure PositiveGram2 where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  determinant_pos : c ^ 2 < a * b

namespace PositiveGram2

variable (g : PositiveGram2)

def firstDiagonal : ℝ := g.a ^ 2 + g.c ^ 2
def secondDiagonal : ℝ := g.b ^ 2 + g.c ^ 2
def offDiagonal : ℝ := g.c * (g.a + g.b)
def lowerSlope : ℝ := g.offDiagonal / g.firstDiagonal
def upperSlope : ℝ := g.secondDiagonal / g.offDiagonal

def denominator (r : ℝ) : ℝ :=
  2 * g.b * g.c * r ^ 2 + (g.a * g.b + 3 * g.c ^ 2) * r + 2 * g.a * g.c

def determinantPolynomial (r : ℝ) : ℝ :=
  r * (g.a ^ 2 + 3 * g.a * g.b + g.b ^ 2 + 3 * g.c ^ 2) -
    g.c * ((3 * g.a + g.b) * r ^ 2 + (g.a + 3 * g.b))

def residualFirst (r : ℝ) : ℝ :=
  g.c ^ 2 * (g.a * g.b * r + g.a * g.c + 2 * g.b ^ 2 * r -
    2 * g.b * g.c * r ^ 2 + 3 * g.b * g.c - 3 * g.c ^ 2 * r) /
    (g.a * g.denominator r)

def residualSecond (r : ℝ) : ℝ :=
  g.c ^ 2 * (2 * g.a ^ 2 * r + g.a * g.b * r + 3 * g.a * g.c * r ^ 2 -
    2 * g.a * g.c + g.b * g.c * r ^ 2 - 3 * g.c ^ 2 * r) /
    (g.b * g.denominator r)

def residualCross (r : ℝ) : ℝ :=
  -(g.c ^ 2 * r * (g.a + g.b)) / g.denominator r

theorem firstDiagonal_pos : 0 < g.firstDiagonal := by
  unfold firstDiagonal
  nlinarith [g.a_pos, sq_nonneg g.c]

theorem secondDiagonal_pos : 0 < g.secondDiagonal := by
  unfold secondDiagonal
  nlinarith [g.b_pos, sq_nonneg g.c]

theorem offDiagonal_pos : 0 < g.offDiagonal :=
  mul_pos g.c_pos (add_pos g.a_pos g.b_pos)

theorem lowerSlope_pos : 0 < g.lowerSlope :=
  div_pos g.offDiagonal_pos g.firstDiagonal_pos

theorem lowerSlope_lt_upperSlope : g.lowerSlope < g.upperSlope := by
  rw [lowerSlope, upperSlope, div_lt_div_iff₀ g.firstDiagonal_pos g.offDiagonal_pos]
  have hd : 0 < (g.a * g.b - g.c ^ 2) ^ 2 := sq_pos_of_pos (sub_pos.mpr g.determinant_pos)
  have hi : g.firstDiagonal * g.secondDiagonal - g.offDiagonal ^ 2 =
      (g.a * g.b - g.c ^ 2) ^ 2 := by
    unfold firstDiagonal secondDiagonal offDiagonal
    ring
  nlinarith

theorem axis_lt_lowerSlope : g.c / g.a < g.lowerSlope := by
  rw [lowerSlope, div_lt_div_iff₀ g.a_pos g.firstDiagonal_pos]
  have hd : 0 < g.c * (g.a * g.b - g.c ^ 2) :=
    mul_pos g.c_pos (sub_pos.mpr g.determinant_pos)
  unfold firstDiagonal offDiagonal
  nlinarith

theorem upperSlope_lt_axis : g.upperSlope < g.b / g.c := by
  rw [upperSlope, div_lt_div_iff₀ g.offDiagonal_pos g.c_pos]
  have hd : 0 < g.c * (g.a * g.b - g.c ^ 2) :=
    mul_pos g.c_pos (sub_pos.mpr g.determinant_pos)
  unfold secondDiagonal offDiagonal
  nlinarith

theorem denominator_pos {r : ℝ} (hr : 0 ≤ r) : 0 < g.denominator r := by
  have ha := g.a_pos
  have hb := g.b_pos
  have hc := g.c_pos
  unfold denominator
  have hfirst : 0 ≤ 2 * g.b * g.c * r ^ 2 := by positivity
  have hsecond : 0 ≤ (g.a * g.b + 3 * g.c ^ 2) * r := by positivity
  have hthird : 0 < 2 * g.a * g.c := by positivity
  linarith

theorem determinantPolynomial_lower :
    g.determinantPolynomial g.lowerSlope =
      g.a * g.c * (g.a * g.b - g.c ^ 2) *
        (g.a ^ 2 + 4 * g.a * g.b + g.b ^ 2 - 2 * g.c ^ 2) /
        (g.a ^ 2 + g.c ^ 2) ^ 2 := by
  have ha : g.a ^ 2 + g.c ^ 2 ≠ 0 := ne_of_gt g.firstDiagonal_pos
  unfold determinantPolynomial lowerSlope firstDiagonal offDiagonal
  field_simp [ha]
  ring

theorem determinantPolynomial_upper :
    g.determinantPolynomial g.upperSlope =
      g.b * (g.a * g.b - g.c ^ 2) *
        (g.a ^ 2 + 4 * g.a * g.b + g.b ^ 2 - 2 * g.c ^ 2) /
        (g.c * (g.a + g.b) ^ 2) := by
  have hc : g.c ≠ 0 := ne_of_gt g.c_pos
  have hab : g.a + g.b ≠ 0 := ne_of_gt (add_pos g.a_pos g.b_pos)
  unfold determinantPolynomial upperSlope secondDiagonal offDiagonal
  field_simp [hc, hab]
  ring

theorem determinantPolynomial_pos {r : ℝ}
    (hl : g.lowerSlope ≤ r) (hr : r ≤ g.upperSlope) :
    0 < g.determinantPolynomial r := by
  have ha := g.a_pos
  have hb := g.b_pos
  have hc := g.c_pos
  have hd : 0 < g.a * g.b - g.c ^ 2 := sub_pos.mpr g.determinant_pos
  have haux : 0 < g.a ^ 2 + 4 * g.a * g.b + g.b ^ 2 - 2 * g.c ^ 2 := by
    have hd := g.determinant_pos
    nlinarith [sq_nonneg (g.a + g.b)]
  have hleft : 0 < g.determinantPolynomial g.lowerSlope := by
    rw [g.determinantPolynomial_lower]
    positivity
  have hright : 0 < g.determinantPolynomial g.upperSlope := by
    rw [g.determinantPolynomial_upper]
    positivity
  have hq (x : ℝ) : g.determinantPolynomial x =
      quadratic (-g.c * (3 * g.a + g.b))
        (g.a ^ 2 + 3 * g.a * g.b + g.b ^ 2 + 3 * g.c ^ 2)
        (-g.c * (g.a + 3 * g.b)) x := by
    unfold determinantPolynomial quadratic
    ring
  rw [hq] at hleft hright ⊢
  have hcoef : -g.c * (3 * g.a + g.b) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by positivity)
  exact quadratic_positive_on_interval _ _ _ _ _ _ hcoef
    g.lowerSlope_lt_upperSlope hl hr hleft hright

theorem residual_determinant (r : ℝ) :
    g.residualFirst r * g.residualSecond r - g.residualCross r ^ 2 =
      g.c ^ 4 * g.determinantPolynomial r /
        (g.a * g.b * g.denominator r) := by
  by_cases hD : g.denominator r = 0
  · simp [residualFirst, residualSecond, residualCross, hD]
  · have ha := ne_of_gt g.a_pos
    have hb := ne_of_gt g.b_pos
    unfold residualFirst residualSecond residualCross determinantPolynomial
    field_simp [ha, hb, hD]
    unfold denominator
    ring

theorem residualFirst_pos {r : ℝ}
    (hl : g.lowerSlope ≤ r) (hr : r ≤ g.upperSlope) :
    0 < g.residualFirst r := by
  have ha := g.a_pos
  have hb := g.b_pos
  have hc := g.c_pos
  have hrpos : 0 < r := lt_of_lt_of_le g.lowerSlope_pos hl
  have hrbound : r < g.b / g.c := lt_of_le_of_lt hr g.upperSlope_lt_axis
  have hbr : 0 < g.b - g.c * r := by
    have := (lt_div_iff₀ hc).mp hrbound
    nlinarith
  have hnum : 0 < g.a * g.b * r + g.a * g.c +
      2 * g.b * r * (g.b - g.c * r) + 3 * g.c * (g.b - g.c * r) := by
    positivity
  have hid : g.a * g.b * r + g.a * g.c + 2 * g.b ^ 2 * r -
      2 * g.b * g.c * r ^ 2 + 3 * g.b * g.c - 3 * g.c ^ 2 * r =
      g.a * g.b * r + g.a * g.c + 2 * g.b * r * (g.b - g.c * r) +
        3 * g.c * (g.b - g.c * r) := by ring
  unfold residualFirst
  rw [hid]
  exact div_pos (mul_pos (sq_pos_of_pos hc) hnum)
    (mul_pos ha (g.denominator_pos hrpos.le))

theorem residual_nonnegative {r : ℝ}
    (hl : g.lowerSlope ≤ r) (hr : r ≤ g.upperSlope) (s t : ℝ) :
    0 ≤ g.residualFirst r * s ^ 2 + 2 * g.residualCross r * s * t +
      g.residualSecond r * t ^ 2 := by
  have ha := g.a_pos
  have hb := g.b_pos
  have hc := g.c_pos
  have hrpos := lt_of_lt_of_le g.lowerSlope_pos hl
  have hD := g.denominator_pos hrpos.le
  have hF := g.determinantPolynomial_pos hl hr
  have hdet : 0 < g.residualFirst r * g.residualSecond r - g.residualCross r ^ 2 := by
    rw [g.residual_determinant]
    positivity
  have hU := g.residualFirst_pos hl hr
  have hn : 0 ≤ (g.residualFirst r * s + g.residualCross r * t) ^ 2 +
      (g.residualFirst r * g.residualSecond r - g.residualCross r ^ 2) * t ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hdet.le (sq_nonneg _))
  have hid : g.residualFirst r * (g.residualFirst r * s ^ 2 +
      2 * g.residualCross r * s * t + g.residualSecond r * t ^ 2) =
      (g.residualFirst r * s + g.residualCross r * t) ^ 2 +
        (g.residualFirst r * g.residualSecond r - g.residualCross r ^ 2) * t ^ 2 := by
    ring
  rw [← hid] at hn
  exact nonneg_of_mul_nonneg_right hn hU

end PositiveGram2

theorem symmetric2_nonnegative (u v w s t : ℝ)
    (hu : 0 < u) (hdet : 0 ≤ u * v - w ^ 2) :
    0 ≤ u * s ^ 2 + 2 * w * s * t + v * t ^ 2 := by
  have hn : 0 ≤ (u * s + w * t) ^ 2 + (u * v - w ^ 2) * t ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg _))
  have hid : u * (u * s ^ 2 + 2 * w * s * t + v * t ^ 2) =
      (u * s + w * t) ^ 2 + (u * v - w ^ 2) * t ^ 2 := by ring
  rw [← hid] at hn
  exact nonneg_of_mul_nonneg_right hn hu

end

end ResearchMain.DiagonalSchatten
