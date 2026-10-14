import MainTheorems.DiagonalSchatten.RationalSVD
import MainTheorems.DiagonalSchatten.TwoRowPowerConnection

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

theorem rationalSVDCore_gram (t w h : ℝ) :
    gramFirst (rationalSVDCore t w h) = (1 + t ^ 2) * (1 + h ^ 2 * w ^ 2) ∧
    gramSecond (rationalSVDCore t w h) = (1 + t ^ 2) * (w ^ 2 + h ^ 2) ∧
    gramCross (rationalSVDCore t w h) = (1 + t ^ 2) * (1 - h ^ 2) * w := by
  simp [gramFirst, gramSecond, gramCross, Fin.sum_univ_two, rationalSVDCore]
  constructor
  · ring
  constructor <;> ring

theorem rationalSVDCore_gap (t w : ℝ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    realGramGap (rationalSVDCore t w h) =
      (1 + t ^ 2) * (1 + w ^ 2) * (1 - h ^ 2) := by
  obtain ⟨ha, hb, hc⟩ := rationalSVDCore_gram t w h
  unfold realGramGap
  rw [ha, hb, hc]
  rw [show ((1 + t ^ 2) * (1 + h ^ 2 * w ^ 2) -
    (1 + t ^ 2) * (w ^ 2 + h ^ 2)) ^ 2 +
    4 * ((1 + t ^ 2) * (1 - h ^ 2) * w) ^ 2 =
    ((1 + t ^ 2) * (1 + w ^ 2) * (1 - h ^ 2)) ^ 2 by ring]
  exact Real.sqrt_sq (mul_nonneg (by positivity) (by nlinarith))

theorem rationalSVDCore_eigenvalues (t w : ℝ) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    realGramPlus (rationalSVDCore t w h) = (1 + t ^ 2) * (1 + w ^ 2) ∧
    realGramMinus (rationalSVDCore t w h) = h ^ 2 * (1 + t ^ 2) * (1 + w ^ 2) := by
  obtain ⟨ha, hb, _⟩ := rationalSVDCore_gram t w h
  have hg := rationalSVDCore_gap t w hh hh1
  constructor
  · change (gramFirst (rationalSVDCore t w h) + gramSecond (rationalSVDCore t w h) +
      realGramGap (rationalSVDCore t w h)) / 2 = _
    rw [ha, hb, hg]
    ring
  · change (gramFirst (rationalSVDCore t w h) + gramSecond (rationalSVDCore t w h) -
      realGramGap (rationalSVDCore t w h)) / 2 = _
    rw [ha, hb, hg]
    ring

theorem rationalSVDCore_gramDet (t w h : ℝ) :
    gramFirst (rationalSVDCore t w h) * gramSecond (rationalSVDCore t w h) -
      gramCross (rationalSVDCore t w h) ^ 2 =
      h ^ 2 * ((1 + t ^ 2) * (1 + w ^ 2)) ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := rationalSVDCore_gram t w h
  rw [ha, hb, hc]
  ring

theorem rationalSVDCore_powerCoefficient (r t w : ℝ) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) :
    realGramPowerCoefficient r (rationalSVDCore t w h) =
      ![((1 + t ^ 2) * (1 + w ^ 2)) ^ r * (1 + w ^ 2 * h ^ (2 * r)) / (1 + w ^ 2),
        ((1 + t ^ 2) * (1 + w ^ 2)) ^ r * (w ^ 2 + h ^ (2 * r)) / (1 + w ^ 2),
        ((1 + t ^ 2) * (1 + w ^ 2)) ^ r * w * (1 - h ^ (2 * r)) / (1 + w ^ 2)] := by
  obtain ⟨ha, hb, hc⟩ := rationalSVDCore_gram t w h
  obtain ⟨hp, hm⟩ := rationalSVDCore_eigenvalues t w hh.le hh1.le
  have hg := rationalSVDCore_gap t w hh.le hh1.le
  have hpow : (h ^ 2 * (1 + t ^ 2) * (1 + w ^ 2)) ^ r =
      h ^ (2 * r) * ((1 + t ^ 2) * (1 + w ^ 2)) ^ r := by
    rw [mul_assoc, Real.mul_rpow (sq_nonneg h) (by positivity),
      ← Real.rpow_natCast_mul hh.le 2]
    norm_num only [Nat.cast_ofNat]
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  have hw : 1 + w ^ 2 ≠ 0 := by positivity
  have hz : 1 - h ^ 2 ≠ 0 := by nlinarith
  ext i
  fin_cases i <;>
    simp [realGramPowerCoefficient, hp, hm, hg, ha, hb, hc, hpow] <;>
    field_simp [ht, hw, hz] <;> ring

theorem rationalSVDCore_power_times_core (r t w : ℝ) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) :
    realGramPowerMatrix r (rationalSVDCore t w h) * rationalSVDCore t w h =
      ((1 + t ^ 2) * (1 + w ^ 2)) ^ r • rationalSVDCore t w (h ^ (2 * r + 1)) := by
  have hc := rationalSVDCore_powerCoefficient r t w hh hh1
  have he : h ^ (2 * r + 1) = h ^ (2 * r) * h := by
    rw [Real.rpow_add hh, Real.rpow_one]
  have hw : 1 + w ^ 2 ≠ 0 := by positivity
  unfold realGramPowerMatrix
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalSVDCore, Matrix.mul_apply, Fin.sum_univ_two, he] <;>
    field_simp [hw] <;> ring

end

end ResearchMain.DiagonalSchatten
