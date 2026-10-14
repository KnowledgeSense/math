import MainTheorems.DiagonalSchatten.ResidualSign

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem signed_symmetric2_trace_positive {s u v w : ℝ}
    (hs : s ≠ 0)
    (hQ : ∀ x y, 0 ≤ s * (u * x ^ 2 + 2 * w * x * y + v * y ^ 2))
    (hn : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) : 0 < s * (u + v) := by
  have hu : 0 ≤ s * u := by simpa using hQ 1 0
  have hv : 0 ≤ s * v := by simpa using hQ 0 1
  have hp : 0 ≤ s * (u + 2 * w + v) := by simpa using hQ 1 1
  have hm : 0 ≤ s * (u - 2 * w + v) := by
    convert! hQ 1 (-1) using 1
    ring
  by_contra ht
  have ht0 : s * (u + v) = 0 := by nlinarith
  have hu0 : s * u = 0 := by nlinarith
  have hv0 : s * v = 0 := by nlinarith
  have hw0 : s * w = 0 := by nlinarith
  have u0 := (mul_eq_zero.mp hu0).resolve_left hs
  have v0 := (mul_eq_zero.mp hv0).resolve_left hs
  have w0 := (mul_eq_zero.mp hw0).resolve_left hs
  rcases hn with hn | hn | hn
  · exact hn u0
  · exact hn v0
  · exact hn w0

namespace ResidualParameters

variable (g : ResidualParameters)

theorem offDiagonal_equal_implies_balance {l r : ℝ}
    (hlr : l ≠ r) (hk : g.k ≠ 0) (hb : g.k + 1 ≠ 0)
    (hc : g.c ≠ 0) (hC : g.cross ≠ 0)
    (hDl : g.denominator l ≠ 0) (hDr : g.denominator r ≠ 0)
    (he : g.offDiagonal l = g.offDiagonal r) : g.a = g.b * l * r := by
  have hd : l * g.denominator r = r * g.denominator l := by
    unfold offDiagonal at he
    field_simp [hDl, hDr] at he
    have hm : g.cross * g.c * (l * g.denominator r - r * g.denominator l) = 0 := by
      nlinarith [he]
    have ht := (mul_eq_zero.mp hm).resolve_left (mul_ne_zero hC hc)
    linarith
  have hfactor : (r - l) * g.k * (g.k + 1) * g.c *
      (g.a - g.b * l * r) = 0 := by
    have heq : l * g.denominator r - r * g.denominator l =
        -(r - l) * g.k * (g.k + 1) * g.c * (g.a - g.b * l * r) := by
      unfold denominator
      ring
    have hd0 : l * g.denominator r - r * g.denominator l = 0 := sub_eq_zero.mpr hd
    rw [heq] at hd0
    linarith
  have hp : (r - l) * g.k * (g.k + 1) * g.c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hlr)) hk) hb) hc
  have hz := (mul_eq_zero.mp hfactor).resolve_left hp
  linarith

theorem symmetric_diagonal_difference (r : ℝ) (ha : g.a ≠ 0)
    (hab : g.a = g.b) (huv : g.u = g.v) (hD : g.denominator r ≠ 0) :
    g.first r - g.second r =
      g.cross * g.c ^ 2 * (g.k + 2) * (1 - r ^ 2) / (g.a * g.denominator r) := by
  unfold first second
  rw [← hab, ← huv]
  field_simp [ha, hD]
  ring

theorem endpoints_not_both_zero {l r : ℝ}
    (hlr : l < r) (hl : 0 < l)
    (ha : 0 < g.a) (hc : g.c ≠ 0) (hC : 0 < g.cross)
    (hk : g.k ≠ 0) (hb : g.k + 1 ≠ 0) (hk2 : 0 < g.k + 2)
    (hDl : 0 < g.denominator l) (hDr : g.denominator r ≠ 0)
    (hbalance : g.a = g.b * l * r → g.a = g.b ∧ g.u = g.v ∧ l < 1) :
    (g.first l ≠ 0 ∨ g.second l ≠ 0 ∨ g.offDiagonal l ≠ 0) ∨
      (g.first r ≠ 0 ∨ g.second r ≠ 0 ∨ g.offDiagonal r ≠ 0) := by
  by_contra hn
  have hfl : g.first l = 0 := by
    by_contra h
    exact hn (Or.inl (Or.inl h))
  have hsl : g.second l = 0 := by
    by_contra h
    exact hn (Or.inl (Or.inr (Or.inl h)))
  have hwl : g.offDiagonal l = 0 := by
    by_contra h
    exact hn (Or.inl (Or.inr (Or.inr h)))
  have hwr : g.offDiagonal r = 0 := by
    by_contra h
    exact hn (Or.inr (Or.inr (Or.inr h)))
  have he : g.offDiagonal l = g.offDiagonal r := hwl.trans hwr.symm
  obtain ⟨hab, huv, hl1⟩ := hbalance
    (g.offDiagonal_equal_implies_balance (ne_of_lt hlr) hk hb hc hC.ne' hDl.ne' hDr he)
  have hd := g.symmetric_diagonal_difference l ha.ne' hab huv hDl.ne'
  have hpos : 0 < g.cross * g.c ^ 2 * (g.k + 2) * (1 - l ^ 2) /
      (g.a * g.denominator l) := by
    have hc2 : 0 < g.c ^ 2 := sq_pos_of_ne_zero hc
    have hl2 : 0 < 1 - l ^ 2 := by nlinarith
    positivity
  rw [hfl, hsl] at hd
  linarith

end ResidualParameters

end

end ResearchMain.DiagonalSchatten
