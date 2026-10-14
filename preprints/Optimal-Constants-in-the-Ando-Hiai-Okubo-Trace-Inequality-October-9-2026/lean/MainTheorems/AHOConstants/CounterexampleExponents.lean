import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

structure CutExponents where
  theta : ℝ
  edges : ℕ
  theta_nonnegative : 0 ≤ theta
  edges_le_one : edges ≤ 1
  capacity_gap : theta + (edges : ℝ) / 2 < 1

noncomputable def CutExponents.height (e : CutExponents) : ℝ :=
  (e.theta / (2 - e.edges) + 1 / 2) / 2

noncomputable def CutExponents.numeratorExponent (e : CutExponents) : ℝ :=
  e.theta + e.edges * e.height

noncomputable def CutExponents.gap (e : CutExponents) : ℝ :=
  2 * e.height - e.numeratorExponent

theorem CutExponents.height_positive (e : CutExponents) : 0 < e.height := by
  rcases e with ⟨theta, edges, htheta, hedges, hgap⟩
  dsimp [CutExponents.height]
  interval_cases edges <;> norm_num at * <;> linarith

theorem CutExponents.height_lt_half (e : CutExponents) : e.height < 1 / 2 := by
  rcases e with ⟨theta, edges, htheta, hedges, hgap⟩
  dsimp [CutExponents.height]
  interval_cases edges <;> norm_num at * <;> linarith

theorem CutExponents.numeratorExponent_nonnegative (e : CutExponents) :
    0 ≤ e.numeratorExponent := by
  dsimp [CutExponents.numeratorExponent]
  exact add_nonneg e.theta_nonnegative (mul_nonneg (Nat.cast_nonneg _) e.height_positive.le)

theorem CutExponents.gap_positive (e : CutExponents) : 0 < e.gap := by
  rcases e with ⟨theta, edges, htheta, hedges, hgap⟩
  dsimp [CutExponents.gap, CutExponents.numeratorExponent, CutExponents.height]
  interval_cases edges <;> norm_num at * <;> linarith

theorem CutExponents.gap_identity (e : CutExponents) :
    e.gap = (2 - e.edges) * e.height - e.theta := by
  dsimp [CutExponents.gap, CutExponents.numeratorExponent]
  ring

theorem small_positive_parameter {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧ epsilon < a ∧ epsilon < b ∧ epsilon < c := by
  let t : ℝ := min 1 (min a (min b c))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₁ : t ≤ 1 := min_le_left _ _
  have hta : t ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have htb : t ≤ b := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have htc : t ≤ c := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨t / 2, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem rpow_below_threshold {epsilon t r : ℝ}
    (he : 0 ≤ epsilon) (ht : 0 < t) (hr : 0 < r) (h : epsilon < t ^ r⁻¹) :
    epsilon ^ r < t := by
  have hp := Real.rpow_lt_rpow he h hr
  rwa [Real.rpow_inv_rpow ht.le (ne_of_gt hr)] at hp

theorem divergent_ratio_parameter {c d delta h L : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hdelta : 0 < delta) (hh : 0 < h) (hL : 0 ≤ L)
    (errorThreshold : ℝ) (herror : 0 < errorThreshold) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
      epsilon ^ h < 1 / 8 ∧ epsilon < errorThreshold ∧
      L < (c / d) * epsilon ^ (-delta) := by
  let target : ℝ := c / (2 * d * (L + 1))
  have htarget : 0 < target := by dsimp [target]; positivity
  have hz : 0 < (1 / 8 : ℝ) ^ h⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have ht : 0 < target ^ delta⁻¹ := Real.rpow_pos_of_pos htarget _
  obtain ⟨epsilon, he, he₁, hez, heerror, het⟩ :=
    small_positive_parameter hz herror ht
  have hep : 0 < epsilon ^ delta := Real.rpow_pos_of_pos he _
  have hepbound : epsilon ^ delta < target :=
    rpow_below_threshold he.le htarget hdelta het
  have hgain : L * epsilon ^ delta < c / d := by
    have hbound : (2 * d * (L + 1)) * epsilon ^ delta < c := by
      apply (lt_div_iff₀ (by positivity : 0 < 2 * d * (L + 1))).1 at hepbound
      nlinarith
    apply (lt_div_iff₀ hd).2
    nlinarith
  refine ⟨epsilon, he, he₁,
    rpow_below_threshold he.le (by norm_num) hh hez, heerror, ?_⟩
  rw [Real.rpow_neg he.le]
  change L < (c / d) / epsilon ^ delta
  exact (lt_div_iff₀ hep).2 hgain

end ResearchMain.AHOConstants
