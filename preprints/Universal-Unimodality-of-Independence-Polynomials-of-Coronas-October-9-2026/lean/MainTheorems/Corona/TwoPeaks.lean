import MainTheorems.Corona.Decay
import MainTheorems.Corona.PeakBounds
import MainTheorems.Corona.Valley

namespace ResearchMain.Corona

open Filter Polynomial

theorem twoPeak_eventually_not_unimodal {h : ℝ[X]} (hh : NonnegativeCoefficients h)
    (hq : 1 ≤ mass h) (hmean : mean h ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ¬Unimodal (fun k => (twoPeakPolynomial h (balanceIndex (mass h) m) m).coeff k) := by
  let D := max h.natDegree 1
  have hD : h.natDegree ≤ D := le_max_left _ _
  have hD1 : 1 ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hq0 : 0 < mass h := by linarith
  let c := separationConstant h
  have hc : 0 < c := separationConstant_positive h hq0 hmean
  obtain ⟨e, he, hec, hesize⟩ := exists_window_width hc hD0
  have hgapcoef : 0 < c - 2 * e := by linarith
  have hR := eventually_linear_ge 1 he
  have hG := eventually_linear_ge 6 hc
  have hseparated := eventually_linear_gt 2 hgapcoef
  have hwindow := eventually_linear_ge (8 * (D : ℝ) ^ 2) (sq_pos_of_pos he)
  have hmeans := eventually_linear_ge (2 / (mass h + 1)) (separationRate_positive hq0)
  have hcorrection := correction_eventually_small h hq0 he
  filter_upwards [hR, hG, hseparated, hwindow, hmeans, hcorrection,
    eventually_ge_atTop (1 : ℕ)] with m hRm hGm hsep hwin hmeansep hcor hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let a := balanceIndex (mass h) m
  let A := leftComponent h a m
  let B := rightComponent h a m
  let C := correction h a m
  have hAm : 0 < mass A := leftComponent_mass_positive h hq0 a m
  have hBm : 0 < mass B := rightComponent_mass_positive h hq0 a m
  have hmass := component_mass_balance h hq m
  have hvar := balanced_variance_bound hh hq0 hD hD1 hm
  have hwindowbound : 4 * (D : ℝ) ^ 2 * m ≤ (e * m) ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hwin hm0.le
    nlinarith only [hmul]
  have hsize : 432 * (e * m) * (4 * (D : ℝ) ^ 2 * m) < (c * m) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hesize (sq_pos_of_pos hm0)
    nlinarith only [hmul]
  have hbetween : 2 * (e * m) + 2 < c * m := by nlinarith only [hsep]
  rw [twoPeakPolynomial_components]
  exact polynomial_not_unimodal (leftComponent_nonnegative hh a m)
    (rightComponent_nonnegative hh a m) (hh.pow (a + 2 * m)) hAm hBm hBm
    hmass ⟨by linarith, le_rfl⟩ hvar.1 hvar.2 hRm
    (hvar.1.trans hwindowbound) (hvar.2.trans hwindowbound) hGm
    (component_mean_separation h hq0 m hmeansep) hbetween hsize (hcor a)

end ResearchMain.Corona
