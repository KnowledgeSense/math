import MainTheorems.DiagonalSchatten.GramBoundary
import Mathlib.Topology.Order.IntermediateValue

namespace ResearchMain.DiagonalSchatten

noncomputable section

structure ResidualParameters where
  a : ℝ
  b : ℝ
  c : ℝ
  cross : ℝ
  k : ℝ
  u : ℝ
  v : ℝ
  w : ℝ

namespace ResidualParameters

variable (g : ResidualParameters)

def denominator (r : ℝ) : ℝ :=
  g.k * ((g.k + 1) * g.a * g.c +
    (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) * r +
    (g.k + 1) * g.b * g.c * r ^ 2)

def first (r : ℝ) : ℝ :=
  g.u + g.cross * g.c * ((g.k + 2) * g.c + (g.k + 1) * g.b * r) /
    (g.a * g.denominator r)

def second (r : ℝ) : ℝ :=
  g.v + g.cross * g.c * ((g.k + 1) * g.a * r + (g.k + 2) * g.c * r ^ 2) /
    (g.b * g.denominator r)

def offDiagonal (r : ℝ) : ℝ := g.w - g.cross * g.c * r / g.denominator r

def leading : ℝ :=
  (g.u * g.v - g.w ^ 2) * g.k * (g.k + 1) * g.b * g.c +
    g.cross * g.c * g.u * (g.k + 2) * g.c / g.b

def linear : ℝ :=
  (g.u * g.v - g.w ^ 2) * g.k * (g.k * g.a * g.b + (g.k + 2) * g.c ^ 2) +
    g.cross * g.c * (g.u * (g.k + 1) * g.a / g.b +
      g.v * (g.k + 1) * g.b / g.a + 2 * g.w) +
    (g.cross * g.c) ^ 2 * (g.k + 2) / (g.a * g.b * g.k)

def constant : ℝ :=
  (g.u * g.v - g.w ^ 2) * g.k * (g.k + 1) * g.a * g.c +
    g.cross * g.c * g.v * (g.k + 2) * g.c / g.a

def determinantNumerator (r : ℝ) : ℝ := quadratic g.leading g.linear g.constant r

theorem determinant_eq (r : ℝ) (ha : g.a ≠ 0) (hb : g.b ≠ 0)
    (hk : g.k ≠ 0) (hD : g.denominator r ≠ 0) :
    g.first r * g.second r - g.offDiagonal r ^ 2 =
      g.determinantNumerator r / g.denominator r := by
  unfold first second offDiagonal determinantNumerator quadratic leading linear constant
  field_simp [ha, hb, hk, hD]
  unfold denominator
  ring

theorem determinant_positive_interior {l r x : ℝ}
    (ha : g.a ≠ 0) (hb : g.b ≠ 0) (hk : g.k ≠ 0)
    (hD : 0 < g.denominator x) (hL : g.leading < 0)
    (hlr : l < r) (hlx : l < x) (hxr : x < r)
    (hl : 0 ≤ g.determinantNumerator l) (hr : 0 ≤ g.determinantNumerator r) :
    0 < g.first x * g.second x - g.offDiagonal x ^ 2 := by
  rw [g.determinant_eq x ha hb hk hD.ne']
  exact div_pos
    (quadratic_positive_on_open_interval _ _ _ _ _ _ hL hlr hlx hxr hl hr) hD

end ResidualParameters

theorem positive_on_interval_of_no_zero {f : ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Set.Icc l r)) (hl : 0 < f l)
    (hzero : ∀ x ∈ Set.Ioo l r, f x ≠ 0) :
    ∀ x ∈ Set.Ioo l r, 0 < f x := by
  intro x hx
  obtain ⟨hlx, hxr⟩ := hx
  by_contra hpos
  have hfx : f x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hzero x ⟨hlx, hxr⟩)
  have hsub : Set.Icc l x ⊆ Set.Icc l r := fun y hy => ⟨hy.1, hy.2.trans hxr.le⟩
  obtain ⟨y, hy, hyzero⟩ := intermediate_value_Icc' hlx.le (hf.mono hsub) ⟨hfx.le, hl.le⟩
  have hyl : l < y := by
    have hyne : y ≠ l := by intro h; subst y; linarith
    exact lt_of_le_of_ne hy.1 (Ne.symm hyne)
  have hyr : y < r := lt_of_le_of_lt hy.2 hxr
  exact hzero y ⟨hyl, hyr⟩ hyzero

theorem symmetric2_trace_positive (u v w s t : ℝ)
    (htr : 0 < u + v) (hdet : 0 < u * v - w ^ 2) :
    0 ≤ u * s ^ 2 + 2 * w * s * t + v * t ^ 2 := by
  have hu : 0 < u := by
    by_contra h
    have hu0 : u ≤ 0 := le_of_not_gt h
    have hv : 0 < v := by linarith
    have huv : u * v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu0 hv.le
    nlinarith [sq_nonneg w]
  exact symmetric2_nonnegative _ _ _ _ _ hu hdet.le

theorem symmetric2_trace_negative (u v w s t : ℝ)
    (htr : u + v < 0) (hdet : 0 < u * v - w ^ 2) :
    u * s ^ 2 + 2 * w * s * t + v * t ^ 2 ≤ 0 := by
  have h := symmetric2_trace_positive (-u) (-v) (-w) s t (by linarith) (by nlinarith)
  linarith

end

end ResearchMain.DiagonalSchatten
