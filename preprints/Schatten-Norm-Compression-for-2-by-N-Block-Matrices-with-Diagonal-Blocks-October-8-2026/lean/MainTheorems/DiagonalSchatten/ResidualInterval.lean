import MainTheorems.DiagonalSchatten.ResidualEndpoints

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem symmetric2_determinant_nonnegative {u v w : ℝ}
    (hQ : ∀ x y, 0 ≤ u * x ^ 2 + 2 * w * x * y + v * y ^ 2) :
    0 ≤ u * v - w ^ 2 := by
  have hu : 0 ≤ u := by simpa using hQ 1 0
  by_cases hu0 : u = 0
  · have hw : w = 0 := by
      by_contra hw
      have h := hQ (-(v + 1) / (2 * w)) 1
      have he : u * (-(v + 1) / (2 * w)) ^ 2 +
          2 * w * (-(v + 1) / (2 * w)) * 1 + v * 1 ^ 2 = -1 := by
        rw [hu0]
        field_simp [hw]
        ring
      rw [he] at h
      norm_num at h
    simp [hu0, hw]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have h := hQ (-w) u
    have he : u * (-w) ^ 2 + 2 * w * (-w) * u + v * u ^ 2 =
        u * (u * v - w ^ 2) := by ring
    rw [he] at h
    exact nonneg_of_mul_nonneg_right h hup

theorem signed_symmetric2_determinant_nonnegative {s u v w : ℝ}
    (hs : s = 1 ∨ s = -1)
    (hQ : ∀ x y, 0 ≤ s * (u * x ^ 2 + 2 * w * x * y + v * y ^ 2)) :
    0 ≤ u * v - w ^ 2 := by
  rcases hs with rfl | rfl
  · exact symmetric2_determinant_nonnegative (by simpa using hQ)
  · have h := symmetric2_determinant_nonnegative (u := -u) (v := -v) (w := -w)
      (fun x y => by convert hQ x y using 1; ring)
    nlinarith

namespace ResidualParameters

variable (g : ResidualParameters)

theorem signed_interval_of_endpoints {s l r : ℝ}
    (hs : s = 1 ∨ s = -1) (hlr : l < r) (hl : 0 < l)
    (ha : 0 < g.a) (hb : g.b ≠ 0) (hc : g.c ≠ 0) (hC : 0 < g.cross)
    (hk : g.k ≠ 0) (hbeta : g.k + 1 ≠ 0) (hk2 : 0 < g.k + 2)
    (hD : ∀ z ∈ Set.Icc l r, 0 < g.denominator z) (hL : g.leading < 0)
    (hbalance : g.a = g.b * l * r → g.a = g.b ∧ g.u = g.v ∧ l < 1)
    (hlQ : ∀ x y, 0 ≤ s * (g.first l * x ^ 2 + 2 * g.offDiagonal l * x * y +
      g.second l * y ^ 2))
    (hrQ : ∀ x y, 0 ≤ s * (g.first r * x ^ 2 + 2 * g.offDiagonal r * x * y +
      g.second r * y ^ 2)) :
    ∀ z ∈ Set.Icc l r, ∀ x y,
      0 ≤ s * (g.first z * x ^ 2 + 2 * g.offDiagonal z * x * y +
        g.second z * y ^ 2) := by
  have hDl := hD l ⟨le_rfl, hlr.le⟩
  have hDr := hD r ⟨hlr.le, le_rfl⟩
  have hF (z : ℝ) (hz : z ∈ Set.Icc l r)
      (hQ : ∀ x y, 0 ≤ s * (g.first z * x ^ 2 + 2 * g.offDiagonal z * x * y +
        g.second z * y ^ 2)) : 0 ≤ g.determinantNumerator z := by
    have hd := signed_symmetric2_determinant_nonnegative hs hQ
    rw [g.determinant_eq z ha.ne' hb hk (hD z hz).ne'] at hd
    rcases div_nonneg_iff.mp hd with hpos | hneg
    · exact hpos.1
    · exact (not_le_of_gt (hD z hz) hneg.2).elim
  have hsn : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have htrace : 0 < s * (g.first l + g.second l) ∨
      0 < s * (g.first r + g.second r) := by
    rcases g.endpoints_not_both_zero hlr hl ha hc hC hk hbeta hk2 hDl hDr.ne' hbalance
        with hleft | hright
    · exact Or.inl (signed_symmetric2_trace_positive hsn hlQ hleft)
    · exact Or.inr (signed_symmetric2_trace_positive hsn hrQ hright)
  exact g.signed_residual_nonnegative hs hlr hD ha.ne' hb hk hL
    (hF l ⟨le_rfl, hlr.le⟩ hlQ) (hF r ⟨hlr.le, le_rfl⟩ hrQ) hlQ hrQ htrace

end ResidualParameters

end

end ResearchMain.DiagonalSchatten
