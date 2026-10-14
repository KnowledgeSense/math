import MainTheorems.DiagonalSchatten.HyperbolicBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ResearchMain.DiagonalSchatten

noncomputable section

def spectralJacobianFactor (p h : ℝ) : ℝ :=
  p ^ 2 * (h ^ (p - 1) - h) ^ 2 - (p - 2) ^ 2 * (1 - h ^ p) ^ 2

theorem exp_difference_sinh (x y : ℝ) :
    Real.exp x - Real.exp y =
      2 * Real.exp ((x + y) / 2) * Real.sinh ((x - y) / 2) := by
  calc
    Real.exp x - Real.exp y =
        Real.exp ((x + y) / 2) * Real.exp ((x - y) / 2) -
          Real.exp ((x + y) / 2) * Real.exp (-((x - y) / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring
    _ = _ := by rw [Real.sinh_eq]; ring

theorem spectralJacobianFactor_sinh {h : ℝ} (hh : 0 < h) (p : ℝ) :
    spectralJacobianFactor p h = 4 * h ^ p *
      (p ^ 2 * Real.sinh ((p - 2) * (-(Real.log h) / 2)) ^ 2 -
        (p - 2) ^ 2 * Real.sinh (p * (-(Real.log h) / 2)) ^ 2) := by
  let s := -(Real.log h) / 2
  have he1 : h ^ (p - 1) - h =
      -(2 * h ^ (p / 2) * Real.sinh ((p - 2) * s)) := by
    have hm : (Real.log h * (p - 1) + Real.log h) / 2 = Real.log h * (p / 2) := by ring
    have hd : (Real.log h * (p - 1) - Real.log h) / 2 = -((p - 2) * s) := by
      dsimp [s]
      ring
    calc
      h ^ (p - 1) - h =
          Real.exp (Real.log h * (p - 1)) - Real.exp (Real.log h) := by
        rw [Real.rpow_def_of_pos hh, Real.exp_log hh]
      _ = _ := by
        rw [exp_difference_sinh, hm, hd, Real.sinh_neg, ← Real.rpow_def_of_pos hh]
        ring
  have he2 : 1 - h ^ p = 2 * h ^ (p / 2) * Real.sinh (p * s) := by
    have hm : (0 + Real.log h * p) / 2 = Real.log h * (p / 2) := by ring
    have hd : (0 - Real.log h * p) / 2 = p * s := by dsimp [s]; ring
    calc
      1 - h ^ p = Real.exp 0 - Real.exp (Real.log h * p) := by
        rw [Real.rpow_def_of_pos hh, Real.exp_zero]
      _ = _ := by rw [exp_difference_sinh, hm, hd, ← Real.rpow_def_of_pos hh]
  have hp : (h ^ (p / 2)) ^ 2 = h ^ p := by
    rw [← Real.rpow_mul_natCast hh.le (p / 2) 2]
    congr 1
    ring
  unfold spectralJacobianFactor
  rw [he1, he2]
  simp only [neg_sq, mul_pow]
  rw [hp]
  ring

theorem spectralJacobianFactor_negative {p h : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) (hh : 0 < h) (hh1 : h < 1) :
    spectralJacobianFactor p h < 0 := by
  let a := |p - 2|
  let s := -(Real.log h) / 2
  have ha : 0 < a := abs_pos.mpr (sub_ne_zero.mpr hp2)
  have hap : a < p := by
    dsimp [a]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hs : 0 < s := by
    dsimp [s]
    linarith [Real.log_neg hh hh1]
  have hb := scaled_sinh_square_strict ha hap hs
  have hea : a ^ 2 = (p - 2) ^ 2 := sq_abs _
  have hes : Real.sinh (a * s) ^ 2 = Real.sinh ((p - 2) * s) ^ 2 := by
    dsimp [a]
    by_cases hn : 0 ≤ p - 2
    · rw [abs_of_nonneg hn]
    · rw [abs_of_neg (lt_of_not_ge hn), neg_mul, Real.sinh_neg, neg_sq]
  rw [hea, hes] at hb
  rw [spectralJacobianFactor_sinh hh p]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Real.rpow_pos_of_pos hh _))
    (sub_neg.mpr hb)

theorem spectralJacobian_power_difference_ne_zero {p h : ℝ}
    (hp2 : p ≠ 2) (hh : 0 < h) (hh1 : h < 1) : h ^ (p - 1) - h ≠ 0 := by
  intro he
  have hp : p - 1 = 1 := (Real.rpow_right_inj hh hh1.ne).mp
    (by simpa only [Real.rpow_one] using (sub_eq_zero.mp he))
  exact hp2 (by linarith)

end

end ResearchMain.DiagonalSchatten
