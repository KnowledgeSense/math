import MainTheorems.DiagonalSchatten.ResidualEndpoints
import MainTheorems.DiagonalSchatten.SpectralCoefficient

namespace ResearchMain.DiagonalSchatten

noncomputable section

def spectralFirst (t theta : ℝ) : ℝ := t + (1 - t) * theta
def spectralSecond (t theta : ℝ) : ℝ := 1 - (1 - t) * theta
def spectralCross (s t theta : ℝ) : ℝ := s * (1 - t) * Real.sqrt (theta * (1 - theta))

def spectralResidual (alpha t theta s : ℝ) : ResidualParameters where
  a := spectralFirst t theta
  b := spectralSecond t theta
  c := spectralCross s t theta
  cross := spectralCross s (t ^ alpha) theta
  k := 2 / alpha
  u := (alpha * theta ^ 2 + alpha * t ^ (alpha - 1) * (1 - theta) ^ 2 +
      2 * ((1 - t ^ alpha) / (1 - t)) * theta * (1 - theta)) / 2 -
    alpha * spectralFirst (t ^ alpha) theta / (2 * spectralFirst t theta)
  v := (alpha * (1 - theta) ^ 2 + alpha * t ^ (alpha - 1) * theta ^ 2 +
      2 * ((1 - t ^ alpha) / (1 - t)) * theta * (1 - theta)) / 2 -
    alpha * spectralSecond (t ^ alpha) theta / (2 * spectralSecond t theta)
  w := theta * (1 - theta) *
    (alpha * (1 + t ^ (alpha - 1)) - 2 * ((1 - t ^ alpha) / (1 - t))) / 2

theorem spectralFirst_pos {t theta : ℝ} (ht : 0 < t)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) : 0 < spectralFirst t theta := by
  have he : spectralFirst t theta = t * (1 - theta) + theta := by
    unfold spectralFirst
    ring
  rw [he]
  by_cases hth : theta = 0
  · simp [hth, ht]
  · have hp : 0 < theta := lt_of_le_of_ne h0 (Ne.symm hth)
    have hterm : 0 ≤ t * (1 - theta) := mul_nonneg ht.le (sub_nonneg.mpr h1)
    linarith

theorem spectralSecond_pos {t theta : ℝ} (ht : 0 < t)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) : 0 < spectralSecond t theta := by
  have he : spectralSecond t theta = spectralFirst t (1 - theta) := by
    unfold spectralFirst spectralSecond
    ring
  rw [he]
  apply spectralFirst_pos ht <;> linarith

theorem spectral_determinant {t theta s : ℝ} (hs : s ^ 2 = 1)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    spectralFirst t theta * spectralSecond t theta - spectralCross s t theta ^ 2 = t := by
  have hr := Real.sq_sqrt (mul_nonneg h0 (sub_nonneg.mpr h1))
  unfold spectralFirst spectralSecond spectralCross
  rw [mul_pow, mul_pow, hs, hr]
  ring

theorem spectral_product_balance (t v theta : ℝ) :
    spectralFirst t theta * spectralFirst v theta -
      spectralSecond t theta * spectralSecond v theta = (2 * theta - 1) * (1 - t * v) := by
  unfold spectralFirst spectralSecond
  ring

theorem spectral_product_balance_unique {alpha t theta : ℝ}
    (ha : 1 < alpha ∨ alpha ≤ -2) (ht : 0 < t) (ht1 : t < 1)
    (he : spectralFirst t theta * spectralFirst (t ^ alpha) theta =
      spectralSecond t theta * spectralSecond (t ^ alpha) theta) : theta = 1 / 2 := by
  have hpow : t * t ^ alpha = t ^ (alpha + 1) := by
    rw [Real.rpow_add ht, Real.rpow_one]
    ring
  have hp : t ^ (alpha + 1) ≠ 1 := by
    rcases ha with ha | ha
    · exact ne_of_lt (Real.rpow_lt_one ht.le ht1 (by linarith))
    · exact ne_of_gt (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht ht1 (by linarith))
  have hzero : (2 * theta - 1) * (1 - t ^ (alpha + 1)) = 0 := by
    rw [← hpow, ← spectral_product_balance, he]
    ring
  have hz := (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr (Ne.symm hp))
  linarith

theorem spectralResidual_symmetric {alpha t s : ℝ} :
    (spectralResidual alpha t (1 / 2) s).a = (spectralResidual alpha t (1 / 2) s).b ∧
      (spectralResidual alpha t (1 / 2) s).u = (spectralResidual alpha t (1 / 2) s).v := by
  have he (v : ℝ) : spectralFirst v (1 / 2) = spectralSecond v (1 / 2) := by
    unfold spectralFirst spectralSecond
    ring
  constructor
  · exact he t
  · simp only [spectralResidual, he]
    ring

theorem spectralResidual_balance_symmetric {alpha t theta s : ℝ}
    (ha : 1 < alpha ∨ alpha ≤ -2) (ht : 0 < t) (ht1 : t < 1)
    (hs : s ^ 2 = 1) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hC : 0 < spectralCross s (t ^ alpha) theta)
    (he : (spectralResidual alpha t theta s).a =
      (spectralResidual alpha t theta s).b *
        (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta) *
        (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta)) :
    (spectralResidual alpha t theta s).a = (spectralResidual alpha t theta s).b ∧
      (spectralResidual alpha t theta s).u = (spectralResidual alpha t theta s).v ∧
      spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta < 1 := by
  have htp : 0 < t ^ alpha := Real.rpow_pos_of_pos ht alpha
  have hA := spectralFirst_pos htp h0 h1
  have hlr : (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta) *
      (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta) =
        spectralSecond (t ^ alpha) theta / spectralFirst (t ^ alpha) theta := by
    field_simp [hA.ne', hC.ne']
  have he' : spectralFirst t theta * spectralFirst (t ^ alpha) theta =
      spectralSecond t theta * spectralSecond (t ^ alpha) theta := by
    change spectralFirst t theta = spectralSecond t theta *
      (spectralCross s (t ^ alpha) theta / spectralFirst (t ^ alpha) theta) *
      (spectralSecond (t ^ alpha) theta / spectralCross s (t ^ alpha) theta) at he
    rw [mul_assoc, hlr, ← mul_div_assoc] at he
    exact (eq_div_iff hA.ne').mp he
  have htheta := spectral_product_balance_unique ha ht ht1 he'
  subst theta
  obtain ⟨hab, huv⟩ := spectralResidual_symmetric (alpha := alpha) (t := t) (s := s)
  refine ⟨hab, huv, ?_⟩
  have habM : spectralFirst (t ^ alpha) (1 / 2) = spectralSecond (t ^ alpha) (1 / 2) := by
    unfold spectralFirst spectralSecond
    ring
  have hd := spectral_determinant (t := t ^ alpha) (theta := 1 / 2) hs
    (by norm_num) (by norm_num)
  rw [← habM] at hd
  apply (div_lt_one hA).mpr
  nlinarith

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem spectralResidual_leading_eq {alpha t theta s : ℝ}
    (ha : alpha ≠ 0) (ht : 0 < t) (ht1 : t ≠ 1)
    (hs : s ^ 2 = 1) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    (spectralResidual alpha t theta s).leading =
      spectralCross s t theta * spectralLeadingRatio alpha t (t ^ (alpha - 1)) theta := by
  have hA := (spectralFirst_pos ht h0 h1).ne'
  have hB := (spectralSecond_pos ht h0 h1).ne'
  have hr := Real.sq_sqrt (mul_nonneg h0 (sub_nonneg.mpr h1))
  have hp : t ^ alpha = t * t ^ (alpha - 1) := by
    simpa only [show alpha - 1 + 1 = alpha by ring] using
      (Real.rpow_add_one ht.ne' (alpha - 1)).trans (mul_comm _ _)
  have hcc : spectralCross s (t ^ alpha) theta * spectralCross s t theta =
      (1 - t ^ alpha) * (1 - t) * theta * (1 - theta) := by
    unfold spectralCross
    calc
      _ = (1 - t ^ alpha) * (1 - t) *
          (s ^ 2 * Real.sqrt (theta * (1 - theta)) ^ 2) := by ring
      _ = _ := by rw [hs, hr]; ring
  let g := spectralResidual alpha t theta s
  have hfactor : g.leading = g.c * ((g.u * g.v - g.w ^ 2) *
      g.k * (g.k + 1) * g.b + (g.cross * g.c) * g.u * (g.k + 2) / g.b) := by
    unfold ResidualParameters.leading
    ring
  change g.leading = _
  rw [hfactor]
  change spectralCross s t theta * _ = spectralCross s t theta * _
  congr 1
  dsimp [g, spectralResidual]
  rw [hcc, hp]
  unfold spectralLeadingRatio spectralFirst spectralSecond at *
  have hD : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  field_simp [ha, hA, hB, hD]

theorem spectralResidual_leading_negative {alpha t theta s : ℝ}
    (ha : 1 < alpha ∨ alpha ≤ -2) (ht : 0 < t) (ht1 : t < 1)
    (hs : s ^ 2 = 1) (h0 : 0 < theta) (h1 : theta < 1)
    (hc : 0 < spectralCross s t theta / alpha) :
    (spectralResidual alpha t theta s).leading < 0 := by
  have han : alpha ≠ 0 := by rcases ha with ha | ha <;> linarith
  rw [spectralResidual_leading_eq han ht (ne_of_lt ht1) hs h0.le h1.le]
  exact spectralLeading_negative ha ht ht1 h0 h1 hc

end

end ResearchMain.DiagonalSchatten
