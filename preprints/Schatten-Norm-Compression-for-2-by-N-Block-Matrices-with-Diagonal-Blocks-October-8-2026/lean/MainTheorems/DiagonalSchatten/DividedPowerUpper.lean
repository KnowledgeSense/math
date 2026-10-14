import MainTheorems.DiagonalSchatten.PowerEnvelope
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace ResearchMain.DiagonalSchatten

noncomputable section

def dividedPower (a t : ℝ) : ℝ := if t = 1 then a else (t ^ a - 1) / (t - 1)

def dividedPowerQuadratic (a t z : ℝ) : ℝ :=
  t * z ^ 2 - (2 * a + 1 + t) * z + a * (a + 2)

def powerDiscriminant (a t : ℝ) : ℝ :=
  (2 * a + 1 + t) ^ 2 - 4 * t * a * (a + 2)

def rationalDenominator (a t : ℝ) : ℝ := a + 1 - (a - 1) * t

def rationalVertexNumerator (a t : ℝ) : ℝ :=
  4 * a * t - (2 * a + 1 + t) * rationalDenominator a t

theorem dividedPowerQuadratic_shift (a t z w : ℝ) :
    dividedPowerQuadratic a t z - dividedPowerQuadratic a t w =
      (z - w) * (t * (z + w) - (2 * a + 1 + t)) := by
  unfold dividedPowerQuadratic
  ring

theorem dividedPowerQuadratic_square (a t z : ℝ) :
    4 * t * dividedPowerQuadratic a t z =
      (2 * t * z - (2 * a + 1 + t)) ^ 2 - powerDiscriminant a t := by
  unfold dividedPowerQuadratic powerDiscriminant
  ring

theorem dividedPowerQuadratic_at_parameter (a t : ℝ) :
    dividedPowerQuadratic a t a = a * (a - 1) * (t - 1) := by
  unfold dividedPowerQuadratic
  ring

theorem dividedPowerQuadratic_at_rational (a t : ℝ)
    (hd : rationalDenominator a t ≠ 0) :
    dividedPowerQuadratic a t (2 * a / rationalDenominator a t) =
      a ^ 2 * (a - 1) * (a + 1) * (t - 1) ^ 2 /
        rationalDenominator a t ^ 2 := by
  unfold dividedPowerQuadratic
  field_simp [hd]
  unfold rationalDenominator
  ring

theorem rationalVertex_negative {a t : ℝ} (ha : 1 < a)
    (ht : 1 < t) (htop : t < (2 * a + 1) / (2 * a - 1))
    (hdisc : 0 ≤ powerDiscriminant a t) :
    rationalVertexNumerator a t < 0 := by
  let b := 2 * a ^ 2 + a - 2
  let q := a * (2 * a + 1) / b
  let top := (2 * a + 1) / (2 * a - 1)
  let v := 2 * a ^ 2 + 2 * a - 1
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have ha1 : 0 < a - 1 := sub_pos.mpr ha
  have hB : 0 < b := by dsimp [b]; nlinarith
  have hD : 0 < 2 * a - 1 := by linarith
  have hq1 : 1 < q := by
    dsimp [q]
    apply (lt_div_iff₀ hB).mpr
    dsimp [b]
    nlinarith
  have hqt : q < top := by
    dsimp [q, top]
    apply (div_lt_div_iff₀ hB hD).mpr
    have hh : 0 < (a - 1) * (2 * a + 1) := by positivity
    dsimp [b]
    nlinarith
  have htv : top < v := by
    have hid : v - top = 2 * a * (a - 1) * (2 * a + 3) / (2 * a - 1) := by
      dsimp [v, top]
      field_simp [hD.ne']
      ring
    have hg : 0 < v - top := by rw [hid]; positivity
    linarith
  have hqdisc : powerDiscriminant a q =
      -4 * (a ^ 2 - 1) * (2 * a + 1) / b ^ 2 := by
    dsimp [q]
    unfold powerDiscriminant
    field_simp [hB.ne']
    dsimp [b]
    ring
  have hqdiscneg : powerDiscriminant a q < 0 := by
    rw [hqdisc]
    have hs : 0 < a ^ 2 - 1 := by nlinarith
    have hn : -4 * (a ^ 2 - 1) * (2 * a + 1) < 0 := by
      have hh : 0 < 4 * (a ^ 2 - 1) * (2 * a + 1) := by positivity
      nlinarith
    exact div_neg_of_neg_of_pos hn (sq_pos_of_pos hB)
  have htq : t < q := by
    by_contra h
    have hqt' : q ≤ t := le_of_not_gt h
    have hid : powerDiscriminant a t - powerDiscriminant a q =
        (t - q) * (t + q - 2 * v) := by
      unfold powerDiscriminant
      dsimp [v]
      ring
    have hco : t + q - 2 * v < 0 := by change t < top at htop; linarith
    have hprod : (t - q) * (t + q - 2 * v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hqt') hco.le
    linarith
  have hqnum : rationalVertexNumerator a q =
      (a - 1) * powerDiscriminant a q := by
    unfold rationalVertexNumerator rationalDenominator powerDiscriminant
    dsimp [q]
    field_simp [hB.ne']
    dsimp [b]
    ring
  have hid : rationalVertexNumerator a t - rationalVertexNumerator a q =
      (t - q) * ((a - 1) * (t + q) + (2 * a ^ 2 + 2 * a - 2)) := by
    unfold rationalVertexNumerator rationalDenominator
    ring
  have hco : 0 < (a - 1) * (t + q) + (2 * a ^ 2 + 2 * a - 2) := by
    have hqpos := lt_trans zero_lt_one hq1
    have hs : 0 < 2 * a ^ 2 + 2 * a - 2 := by nlinarith
    positivity
  have hprod : (t - q) * ((a - 1) * (t + q) + (2 * a ^ 2 + 2 * a - 2)) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr htq) hco
  have hqn : rationalVertexNumerator a q < 0 := by
    rw [hqnum]
    exact mul_neg_of_pos_of_neg ha1 hqdiscneg
  linarith

theorem dividedPowerQuadratic_positive {a t : ℝ} (ha : 1 < a)
    (ht : 0 < t) (hneq : t ≠ 1) :
    0 < dividedPowerQuadratic a t (dividedPower a t) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have ha1 : 0 < a - 1 := sub_pos.mpr ha
  have hta : 1 + a * (t - 1) ≤ t ^ a := by
    have h := one_add_mul_self_le_rpow_one_add (s := t - 1) (by linarith) ha.le
    simpa only [show 1 + (t - 1) = t by ring] using h
  let z := dividedPower a t
  have hz : z = (t ^ a - 1) / (t - 1) := by simp [z, dividedPower, hneq]
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hd : 0 < rationalDenominator a t := by
      unfold rationalDenominator
      have hh : 0 < (a - 1) * (1 - t) := mul_pos ha1 (sub_pos.mpr hlt)
      nlinarith
    let r := 2 * a / rationalDenominator a t
    have hzr : z < r := by rw [hz]; exact divided_power_rational_upper ha ht hneq hd
    have hra : r < a := by
      apply (div_lt_iff₀ hd).mpr
      have hh : 0 < a * ((a - 1) * (1 - t)) := by positivity
      unfold rationalDenominator
      nlinarith
    have hco : t * (z + r) - (2 * a + 1 + t) < 0 := by
      have hh : 0 < 2 * a * (1 - t) := by positivity
      nlinarith
    have hrQ : 0 < dividedPowerQuadratic a t r := by
      rw [dividedPowerQuadratic_at_rational a t hd.ne']
      have hs : 0 < (t - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)
      positivity
    have hdiff := dividedPowerQuadratic_shift a t z r
    have hprod := mul_pos_of_neg_of_neg (sub_neg.mpr hzr) hco
    change 0 < dividedPowerQuadratic a t z
    linarith
  · have hza : a ≤ z := by
      rw [hz]
      apply (le_div_iff₀ (sub_pos.mpr hgt)).mpr
      linarith
    by_cases hlarge : (2 * a + 1) / (2 * a - 1) ≤ t
    · have hD : 0 < 2 * a - 1 := by linarith
      have hh := (div_le_iff₀ hD).mp hlarge
      have hco : 0 ≤ t * (z + a) - (2 * a + 1 + t) := by
        nlinarith
      have hbase : 0 < dividedPowerQuadratic a t a := by
        rw [dividedPowerQuadratic_at_parameter]
        positivity
      have hdiff := dividedPowerQuadratic_shift a t z a
      have hprod := mul_nonneg (sub_nonneg.mpr hza) hco
      change 0 < dividedPowerQuadratic a t z
      linarith
    · have htop := lt_of_not_ge hlarge
      by_cases hdisc : powerDiscriminant a t < 0
      · have hsq := dividedPowerQuadratic_square a t z
        have hs := sq_nonneg (2 * t * z - (2 * a + 1 + t))
        change 0 < dividedPowerQuadratic a t z
        nlinarith
      · have hdisc' : 0 ≤ powerDiscriminant a t := le_of_not_gt hdisc
        have hnum := rationalVertex_negative ha hgt htop hdisc'
        have hD : 0 < 2 * a - 1 := by linarith
        have htbound := (lt_div_iff₀ hD).mp htop
        have hd : 0 < rationalDenominator a t := by
          unfold rationalDenominator
          nlinarith
        let r := 2 * a / rationalDenominator a t
        have hzr : z < r := by rw [hz]; exact divided_power_rational_upper ha ht hneq hd
        have hvertex : 2 * t * r < 2 * a + 1 + t := by
          have hh : 2 * t * r = 4 * a * t / rationalDenominator a t := by dsimp [r]; ring
          rw [hh]
          apply (div_lt_iff₀ hd).mpr
          unfold rationalVertexNumerator at hnum
          linarith
        have hco : t * (z + r) - (2 * a + 1 + t) < 0 := by nlinarith
        have hrQ : 0 < dividedPowerQuadratic a t r := by
          rw [dividedPowerQuadratic_at_rational a t hd.ne']
          have hs : 0 < (t - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)
          positivity
        have hdiff := dividedPowerQuadratic_shift a t z r
        have hprod := mul_pos_of_neg_of_neg (sub_neg.mpr hzr) hco
        change 0 < dividedPowerQuadratic a t z
        linarith

end

end ResearchMain.DiagonalSchatten
