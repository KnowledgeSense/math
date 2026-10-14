import MainTheorems.DiagonalSchatten.HyperbolicPower
import MainTheorems.DiagonalSchatten.NegativePowerBounds

namespace ResearchMain.DiagonalSchatten

noncomputable section

def lowerDiscriminant (m t : ℝ) : ℝ :=
  (t + 1 - 2 * m) ^ 2 - 4 * t * m * (m - 2)

theorem lowerPowerQuadratic_square (m t y : ℝ) :
    4 * t * lowerPowerQuadratic m t y =
      (2 * t * y + (t + 1 - 2 * m)) ^ 2 - lowerDiscriminant m t := by
  unfold lowerPowerQuadratic lowerDiscriminant
  ring

theorem lower_middle_discriminant_bound {m t : ℝ}
    (hm : 2 ≤ m) (ht : 1 < t) (htop : t < 2 * m - 1)
    (hdisc : 0 ≤ lowerDiscriminant m t) :
    (m * (m - 1) - 1) * (t - 1) < 2 := by
  let h := m * (m - 1) - 1
  let u := t - 1
  have hm0 : 0 < m := by linarith
  have hm2 : 0 ≤ m - 2 := by linarith
  have h1 : 1 ≤ h := by dsimp [h]; nlinarith
  have hh0 : 0 < h := lt_of_lt_of_le zero_lt_one h1
  have hmu : m - 1 ≤ h := by
    have hp := mul_nonneg hm0.le hm2
    dsimp [h]
    nlinarith
  have hu0 : 0 < u := sub_pos.mpr ht
  have huUpper : u < 2 * h := by dsimp [u]; linarith
  have hdiscEq : lowerDiscriminant m t = 4 - 4 * h * u + u ^ 2 := by
    unfold lowerDiscriminant
    dsimp [h, u]
    ring
  let q := 2 / h
  have hqpos : 0 < q := div_pos (by norm_num) hh0
  have hqle : q ≤ 2 * h := by
    apply (div_le_iff₀ hh0).mpr
    nlinarith
  have hqEq : 4 - 4 * h * q + q ^ 2 = -4 + 4 / h ^ 2 := by
    dsimp [q]
    field_simp [hh0.ne']
    ring
  by_contra hneg
  have hfail : 2 ≤ h * u := le_of_not_gt hneg
  have hqu : q ≤ u := (div_le_iff₀ hh0).mpr (by nlinarith)
  by_cases heq : h = 1
  · have hq : q = 2 := by simp [q, heq]
    have hM : m = 2 := by dsimp [h] at heq; nlinarith
    dsimp [u] at hqu
    rw [hq] at hqu
    linarith
  · have hh1 : 1 < h := lt_of_le_of_ne h1 (Ne.symm heq)
    have hqDisc : 4 - 4 * h * q + q ^ 2 < 0 := by
      rw [hqEq]
      have hsq : 1 < h ^ 2 := by nlinarith
      have hi : 4 / h ^ 2 < 4 := (div_lt_iff₀ (sq_pos_of_pos hh0)).mpr (by nlinarith)
      linarith
    have hid : (4 - 4 * h * u + u ^ 2) - (4 - 4 * h * q + q ^ 2) =
        (u - q) * (u + q - 4 * h) := by ring
    have hco : u + q - 4 * h < 0 := by linarith
    have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hqu) hco.le
    rw [hdiscEq] at hdisc
    linarith

theorem baseline_vertex_positive {m t : ℝ}
    (hm : 2 ≤ m) (ht : 1 < t) (htop : t < 2 * m - 1)
    (hdisc : 0 ≤ lowerDiscriminant m t) :
    0 < 2 * t * (m * t ^ (-(m + 1) / 2)) + (t + 1 - 2 * m) := by
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hs := negative_power_tangent (r := (1 - m) / 2) (by linarith) ht0
  have hbound := lower_middle_discriminant_bound hm ht htop hdisc
  have hp : t * t ^ (-(m + 1) / 2) = t ^ ((1 - m) / 2) := by
    calc
      t * t ^ (-(m + 1) / 2) = t ^ (1 : ℝ) * t ^ (-(m + 1) / 2) := by rw [Real.rpow_one]
      _ = t ^ (1 + -(m + 1) / 2) := (Real.rpow_add ht0 _ _).symm
      _ = t ^ ((1 - m) / 2) := congrArg (fun r : ℝ => t ^ r) (by ring)
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * m by positivity)
  rw [show 2 * t * (m * t ^ (-(m + 1) / 2)) =
    2 * m * (t * t ^ (-(m + 1) / 2)) by ring, hp]
  nlinarith

theorem lowerPowerQuadratic_positive_of_ge_baseline {m t y : ℝ}
    (hm : 2 ≤ m) (ht : 0 < t) (hneq : t ≠ 1)
    (hy : m * t ^ (-(m + 1) / 2) ≤ y) :
    0 < lowerPowerQuadratic m t y := by
  let Y := m * t ^ (-(m + 1) / 2)
  have hy' : Y ≤ y := hy
  have hm0 : 0 < m := by linarith
  have hYpos : 0 < Y := mul_pos hm0 (Real.rpow_pos_of_pos ht _)
  have hbase := lowerPowerQuadratic_baseline_positive hm ht hneq
  have hshift : lowerPowerQuadratic m t y - lowerPowerQuadratic m t Y =
      (y - Y) * (t * (y + Y) + (t + 1 - 2 * m)) := by
    unfold lowerPowerQuadratic
    ring
  have hproduct (hvertex : 0 ≤ 2 * t * Y + (t + 1 - 2 * m)) :
      0 < lowerPowerQuadratic m t y := by
    have hco : 0 ≤ t * (y + Y) + (t + 1 - 2 * m) := by nlinarith [hy']
    have hmul := mul_nonneg (sub_nonneg.mpr hy') hco
    change 0 < lowerPowerQuadratic m t Y at hbase
    linarith
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hr : (1 - m) / 2 < 0 := by linarith
    have hlog : Real.log t < 0 := Real.log_neg ht hlt
    have hexp : 1 < t ^ ((1 - m) / 2) := by
      rw [Real.rpow_def_of_pos ht]
      have hpos : 0 < Real.log t * ((1 - m) / 2) := mul_pos_of_neg_of_neg hlog hr
      simpa using Real.exp_lt_exp.mpr hpos
    have hp : t * t ^ (-(m + 1) / 2) = t ^ ((1 - m) / 2) := by
      calc
        t * t ^ (-(m + 1) / 2) = t ^ (1 : ℝ) * t ^ (-(m + 1) / 2) := by rw [Real.rpow_one]
        _ = t ^ (1 + -(m + 1) / 2) := (Real.rpow_add ht _ _).symm
        _ = t ^ ((1 - m) / 2) := congrArg (fun r : ℝ => t ^ r) (by ring)
    apply hproduct
    dsimp [Y]
    rw [show 2 * t * (m * t ^ (-(m + 1) / 2)) =
      2 * m * (t * t ^ (-(m + 1) / 2)) by ring, hp]
    have hmul := mul_lt_mul_of_pos_left hexp (show 0 < 2 * m by positivity)
    linarith
  · by_cases hlarge : 2 * m - 1 ≤ t
    · apply hproduct
      have hp := mul_pos ht hYpos
      linarith
    · have htop : t < 2 * m - 1 := lt_of_not_ge hlarge
      by_cases hdisc : lowerDiscriminant m t < 0
      · have hsq := lowerPowerQuadratic_square m t y
        have hn := sq_nonneg (2 * t * y + (t + 1 - 2 * m))
        nlinarith
      · exact hproduct (baseline_vertex_positive hm hgt htop (le_of_not_gt hdisc)).le

theorem negative_divided_power_quadratic_positive {m t : ℝ}
    (hm : 2 ≤ m) (ht : 0 < t) (hneq : t ≠ 1) :
    0 < lowerPowerQuadratic m t ((1 - t ^ (-m)) / (t - 1)) :=
  lowerPowerQuadratic_positive_of_ge_baseline hm ht hneq
    (negative_divided_power_ge_baseline (le_trans (by norm_num) hm) ht hneq)

end

end ResearchMain.DiagonalSchatten
