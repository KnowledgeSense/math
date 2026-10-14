import MainTheorems.DiagonalSchatten.TanhBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem tanh_exp_neg_two (x : ℝ) :
    Real.tanh x = (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)) := by
  rw [Real.tanh_eq]
  apply (div_eq_div_iff (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
    (by positivity : 1 + Real.exp (-2 * x) ≠ 0)).mpr
  have he : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

theorem tanh_log_power {h : ℝ} (hh : 0 < h) (q : ℝ) :
    Real.tanh (q * (-(Real.log h) / 2)) = (1 - h ^ q) / (1 + h ^ q) := by
  rw [tanh_exp_neg_two, Real.rpow_def_of_pos hh]
  rw [show -2 * (q * (-Real.log h / 2)) = Real.log h * q by ring]

def symmetricDiagonalBracket (q h : ℝ) : ℝ :=
  (1 + h) * (1 - h ^ q) - q * (1 - h) * (1 + h ^ q)

def symmetricOffDiagonalBracket (q h : ℝ) : ℝ :=
  (1 - h) * (1 + h ^ q) - q * (1 + h) * (1 - h ^ q)

theorem symmetricDiagonalBracket_positive {q h : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hh : 0 < h) (hh1 : h < 1) : 0 < symmetricDiagonalBracket q h := by
  have hx : 0 < -(Real.log h) / 2 := by linarith [Real.log_neg hh hh1]
  have ht := tanh_scale_between_zero_one hq hq1 hx
  rw [tanh_log_power hh q] at ht
  have he : Real.tanh (-(Real.log h) / 2) = (1 - h) / (1 + h) := by
    simpa only [one_mul, Real.rpow_one] using tanh_log_power hh 1
  rw [he] at ht
  have hqpow : 0 < h ^ q := Real.rpow_pos_of_pos hh q
  have hmul := (div_lt_div_iff₀ (by positivity : 0 < 1 + h)
    (by positivity : 0 < 1 + h ^ q)).mp
      (show q * (1 - h) / (1 + h) < (1 - h ^ q) / (1 + h ^ q) by
        simpa only [mul_div_assoc] using ht)
  unfold symmetricDiagonalBracket
  nlinarith

theorem symmetricDiagonalBracket_negative {q h : ℝ} (hq : 1 < q)
    (hh : 0 < h) (hh1 : h < 1) : symmetricDiagonalBracket q h < 0 := by
  have hx : 0 < -(Real.log h) / 2 := by linarith [Real.log_neg hh hh1]
  have ht := tanh_scale_strict hq hx
  rw [tanh_log_power hh q] at ht
  have he : Real.tanh (-(Real.log h) / 2) = (1 - h) / (1 + h) := by
    simpa only [one_mul, Real.rpow_one] using tanh_log_power hh 1
  rw [he] at ht
  have hqpow : 0 < h ^ q := Real.rpow_pos_of_pos hh q
  have hmul := (div_lt_div_iff₀ (by positivity : 0 < 1 + h ^ q)
    (by positivity : 0 < 1 + h)).mp
      (show (1 - h ^ q) / (1 + h ^ q) < q * (1 - h) / (1 + h) by
        simpa only [mul_div_assoc] using ht)
  unfold symmetricDiagonalBracket
  nlinarith

theorem symmetricOffDiagonalBracket_positive {q h : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hh : 0 < h) (hh1 : h < 1) : 0 < symmetricOffDiagonalBracket q h := by
  have hp : h < h ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hh hh1 hq1
  have hp1 : h ^ q < 1 := Real.rpow_lt_one hh.le hh1 hq
  have hn : 0 < (1 + h) * (1 - h ^ q) := mul_pos (by positivity) (sub_pos.mpr hp1)
  unfold symmetricOffDiagonalBracket
  nlinarith

theorem symmetricOffDiagonalBracket_negative {q h : ℝ} (hq : 1 < q)
    (hh : 0 < h) (hh1 : h < 1) : symmetricOffDiagonalBracket q h < 0 := by
  have hp : h ^ q < h := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hh hh1 hq
  have hp1 : h ^ q < 1 := hp.trans hh1
  have hn : 0 < (1 + h) * (1 - h ^ q) := mul_pos (by positivity) (sub_pos.mpr hp1)
  unfold symmetricOffDiagonalBracket
  nlinarith

end

end ResearchMain.DiagonalSchatten
