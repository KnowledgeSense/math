import MainTheorems.Corona.PeakParameters
import Mathlib.Analysis.SpecificLimits.Normed

namespace ResearchMain.Corona

open Filter Polynomial

theorem eventually_linear_ge (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, a ≤ c * m := by
  have ht : ∀ᶠ m : ℕ in atTop, a / c ≤ (m : ℝ) :=
    (eventually_ge_atTop (a / c)).natCast_atTop
  filter_upwards [ht] with m hm
  have h := (div_le_iff₀ hc).mp hm
  nlinarith only [h]

theorem eventually_linear_gt (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, a < c * m := by
  have ht : ∀ᶠ m : ℕ in atTop, a / c < (m : ℝ) :=
    (eventually_gt_atTop (a / c)).natCast_atTop
  filter_upwards [ht] with m hm
  have h := (div_lt_iff₀ hc).mp hm
  nlinarith only [h]

theorem correction_mass_bound (h : ℝ[X]) (hq : 0 < mass h) {e : ℝ} (he : 0 < e)
    {a m : ℕ} (hm : 0 < m)
    (hsmall : (m : ℝ) * ((1 + 2 / mass h)⁻¹) ^ m ≤ 1 / (24 * e)) :
    mass (correction h a m) ≤ mass (rightComponent h a m) / (24 * (e * m)) := by
  have hv : 0 < 1 + 2 / mass h := by positivity
  have hscaled := (le_div_iff₀ (by positivity : 0 < 24 * e)).mp hsmall
  have hid : (m : ℝ) * ((1 + 2 / mass h)⁻¹) ^ m * (24 * e) =
      24 * (e * m) / (1 + 2 / mass h) ^ m := by rw [inv_pow]; ring
  rw [hid] at hscaled
  have hpow := (div_le_iff₀ (pow_pos hv m)).mp hscaled
  simp only [one_mul] at hpow
  rw [correction, mass_pow, rightComponent_balanced_mass _ _ _ (ne_of_gt hq)]
  apply (le_div_iff₀ (by positivity : 0 < 24 * (e * m))).mpr
  exact mul_le_mul_of_nonneg_left hpow (pow_nonneg hq.le _)

theorem correction_eventually_small (h : ℝ[X]) (hq : 0 < mass h) {e : ℝ} (he : 0 < e) :
    ∀ᶠ m : ℕ in atTop, ∀ a : ℕ,
      mass (correction h a m) ≤ mass (rightComponent h a m) / (24 * (e * m)) := by
  have hv : 1 < 1 + 2 / mass h := by
    have hd : (0 : ℝ) < 2 / mass h := by positivity
    linarith
  have hr0 : 0 ≤ (1 + 2 / mass h)⁻¹ := by positivity
  have hr1 : (1 + 2 / mass h)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hv
  have ht := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hsmall : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) * ((1 + 2 / mass h)⁻¹) ^ m < 1 / (24 * e) :=
    ht.eventually_lt_const (by positivity)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with m hsm hm
  exact fun a => correction_mass_bound h hq he hm hsm.le

theorem exists_window_width {c D : ℝ} (hc : 0 < c) (hD : 0 < D) :
    ∃ e : ℝ, 0 < e ∧ 2 * e < c ∧ 1728 * e * D ^ 2 < c ^ 2 := by
  let e := min (c / 8) (c ^ 2 / (4096 * D ^ 2))
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have he₁ : e ≤ c / 8 := min_le_left _ _
  have he₂ : e ≤ c ^ 2 / (4096 * D ^ 2) := min_le_right _ _
  have hscaled := (le_div_iff₀ (by positivity : 0 < 4096 * D ^ 2)).mp he₂
  have hpos : 0 < e * D ^ 2 := mul_pos he (sq_pos_of_pos hD)
  exact ⟨e, he, by linarith, by nlinarith only [hscaled, hpos]⟩

end ResearchMain.Corona
