import MainTheorems.DiagonalSchatten.GeneralResidual

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem positive_on_interval_of_no_zero_right {f : ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Set.Icc l r)) (hr : 0 < f r)
    (hzero : ∀ x ∈ Set.Ioo l r, f x ≠ 0) :
    ∀ x ∈ Set.Ioo l r, 0 < f x := by
  have hmap : Set.MapsTo (fun x : ℝ => l + r - x) (Set.Icc l r) (Set.Icc l r) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hc : ContinuousOn (fun x : ℝ => f (l + r - x)) (Set.Icc l r) :=
    hf.comp (by fun_prop) hmap
  have hp := positive_on_interval_of_no_zero hc (by simpa using hr)
    (fun x hx => hzero (l + r - x) (by constructor <;> linarith [hx.1, hx.2]))
  intro x hx
  have hm : l + r - x ∈ Set.Ioo l r := by
    constructor <;> linarith [hx.1, hx.2]
  simpa using hp (l + r - x) hm

theorem symmetric2_signed_nonnegative {s u v w : ℝ} (hs : s = 1 ∨ s = -1)
    (htr : 0 < s * (u + v)) (hdet : 0 < u * v - w ^ 2) (x y : ℝ) :
    0 ≤ s * (u * x ^ 2 + 2 * w * x * y + v * y ^ 2) := by
  rcases hs with rfl | rfl
  · simpa using symmetric2_trace_positive u v w x y (by simpa using htr) hdet
  · have ht : u + v < 0 := by linarith
    have h := symmetric2_trace_negative u v w x y ht hdet
    linarith

namespace ResidualParameters

variable (g : ResidualParameters)

theorem continuousOn_trace {l r : ℝ}
    (ha : g.a ≠ 0) (hb : g.b ≠ 0)
    (hD : ∀ x ∈ Set.Icc l r, g.denominator x ≠ 0) :
    ContinuousOn (fun x => g.first x + g.second x) (Set.Icc l r) := by
  have hden : ContinuousOn g.denominator (Set.Icc l r) := by unfold denominator; fun_prop
  have hfirst : ContinuousOn g.first (Set.Icc l r) := by
    unfold first
    exact continuousOn_const.add
      ((show ContinuousOn (fun x : ℝ => g.cross * g.c *
          ((g.k + 2) * g.c + (g.k + 1) * g.b * x)) (Set.Icc l r) by fun_prop).div
        (continuousOn_const.mul hden) (fun x hx => mul_ne_zero ha (hD x hx)))
  have hsecond : ContinuousOn g.second (Set.Icc l r) := by
    unfold second
    exact continuousOn_const.add
      ((show ContinuousOn (fun x : ℝ => g.cross * g.c *
          ((g.k + 1) * g.a * x + (g.k + 2) * g.c * x ^ 2)) (Set.Icc l r) by fun_prop).div
        (continuousOn_const.mul hden) (fun x hx => mul_ne_zero hb (hD x hx)))
  exact hfirst.add hsecond

theorem trace_ne_zero {x : ℝ}
    (hd : 0 < g.first x * g.second x - g.offDiagonal x ^ 2) :
    g.first x + g.second x ≠ 0 := by
  intro ht
  have he : g.second x = -g.first x := by linarith
  rw [he] at hd
  nlinarith [sq_nonneg (g.first x), sq_nonneg (g.offDiagonal x)]

theorem signed_residual_nonnegative {s l r : ℝ}
    (hs : s = 1 ∨ s = -1) (hlr : l < r)
    (hD : ∀ x ∈ Set.Icc l r, 0 < g.denominator x)
    (ha : g.a ≠ 0) (hb : g.b ≠ 0) (hk : g.k ≠ 0)
    (hL : g.leading < 0)
    (hlF : 0 ≤ g.determinantNumerator l) (hrF : 0 ≤ g.determinantNumerator r)
    (hlQ : ∀ x y, 0 ≤ s * (g.first l * x ^ 2 + 2 * g.offDiagonal l * x * y +
      g.second l * y ^ 2))
    (hrQ : ∀ x y, 0 ≤ s * (g.first r * x ^ 2 + 2 * g.offDiagonal r * x * y +
      g.second r * y ^ 2))
    (htrace : 0 < s * (g.first l + g.second l) ∨
      0 < s * (g.first r + g.second r)) :
    ∀ z ∈ Set.Icc l r, ∀ x y,
      0 ≤ s * (g.first z * x ^ 2 + 2 * g.offDiagonal z * x * y +
        g.second z * y ^ 2) := by
  have hsn : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hd (z : ℝ) (hz : z ∈ Set.Ioo l r) :
      0 < g.first z * g.second z - g.offDiagonal z ^ 2 :=
    g.determinant_positive_interior ha hb hk (hD z ⟨hz.1.le, hz.2.le⟩)
      hL hlr hz.1 hz.2 hlF hrF
  have hc : ContinuousOn (fun z => s * (g.first z + g.second z)) (Set.Icc l r) :=
    continuousOn_const.mul (g.continuousOn_trace ha hb (fun z hz => (hD z hz).ne'))
  have hn : ∀ z ∈ Set.Ioo l r, s * (g.first z + g.second z) ≠ 0 :=
    fun z hz => mul_ne_zero hsn (g.trace_ne_zero (hd z hz))
  have ht : ∀ z ∈ Set.Ioo l r, 0 < s * (g.first z + g.second z) := by
    rcases htrace with hl | hr
    · exact positive_on_interval_of_no_zero hc hl hn
    · exact positive_on_interval_of_no_zero_right hc hr hn
  intro z hz x y
  rcases eq_or_lt_of_le hz.1 with rfl | hlz
  · exact hlQ x y
  rcases eq_or_lt_of_le hz.2 with rfl | hzr
  · exact hrQ x y
  · exact symmetric2_signed_nonnegative hs (ht z ⟨hlz, hzr⟩) (hd z ⟨hlz, hzr⟩) x y

end ResidualParameters

end

end ResearchMain.DiagonalSchatten
