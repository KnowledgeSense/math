import MainTheorems.DiagonalSchatten.ScalarCertificates

namespace ResearchMain.DiagonalSchatten

noncomputable section

def rawPowerOne (a t h : ℝ) : ℝ :=
  -a ^ 2 * (t - 1) ^ 2 + 2 * a * t * (t - 1) * (h - 1) -
    t ^ 3 * h ^ 2 + t * (t ^ 2 + 2 * t - 1) * h - t ^ 2 - t + 1

def rawPowerZero (a t h : ℝ) : ℝ :=
  -a ^ 2 * h ^ 2 * t * (t - 1) ^ 2 + 2 * a * h * t * (t - 1) * (h - 1) +
    h ^ 2 * t * (t ^ 2 - t - 1) + h * (-t ^ 2 + 2 * t + 1) - 1

def spectralLeadingRatio (a t h theta : ℝ) : ℝ :=
  let A := t + (1 - t) * theta
  let B := 1 - (1 - t) * theta
  let E := (1 - t * h) / (1 - t)
  let M1 := t * h + (1 - t * h) * theta
  let M2 := 1 - (1 - t * h) * theta
  let U := (a * theta ^ 2 + a * h * (1 - theta) ^ 2 + 2 * E * theta * (1 - theta)) / 2 -
    a * M1 / (2 * A)
  let V := (a * (1 - theta) ^ 2 + a * h * theta ^ 2 + 2 * E * theta * (1 - theta)) / 2 -
    a * M2 / (2 * B)
  let W := theta * (1 - theta) * (a * (1 + h) - 2 * E) / 2
  (U * V - W ^ 2) * (2 / a) * (2 / a + 1) * B +
    (1 - t * h) * (1 - t) * theta * (1 - theta) * U * (2 / a + 2) / B

theorem rawPowerZero_reciprocal (a t h : ℝ) (ht : t ≠ 0) (hh : h ≠ 0) :
    rawPowerZero a t h = t ^ 3 * h ^ 2 * rawPowerOne a (1 / t) (1 / h) := by
  unfold rawPowerZero rawPowerOne
  field_simp [ht, hh]
  ring

theorem rawPowerOne_actual (a : ℝ) {t : ℝ} (ht : 0 < t) (hneq : t ≠ 1) :
    rawPowerOne a t (t ^ (a - 1)) = powerCertificate a t := by
  have hpower : t ^ a = t * t ^ (a - 1) := by
    calc
      t ^ a = t ^ (1 + (a - 1)) := congrArg (fun r : ℝ => t ^ r) (by ring)
      _ = t * t ^ (a - 1) := by rw [Real.rpow_add ht, Real.rpow_one]
  unfold powerCertificate dividedPowerQuadratic dividedPower
  rw [ite_eq_right hneq, hpower]
  unfold rawPowerOne
  field_simp [sub_ne_zero.mpr hneq]
  ring

theorem rawPowerZero_actual (a : ℝ) {t : ℝ} (ht : 0 < t) (hneq : t ≠ 1) :
    rawPowerZero a t (t ^ (a - 1)) = reciprocalPowerCertificate a t := by
  have hh : 0 < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
  have hr : 1 / t ≠ 1 := by
    intro h
    have ht1 := (div_eq_iff ht.ne').mp h
    exact hneq (by linarith)
  have hrec : (1 / t) ^ (a - 1) = 1 / t ^ (a - 1) := by
    simp only [one_div, Real.inv_rpow ht.le]
  have hweight : t ^ (2 * a + 1) = t ^ 3 * (t ^ (a - 1)) ^ 2 := by
    calc
      t ^ (2 * a + 1) = t ^ (3 + (a - 1) * (2 : ℝ)) :=
        congrArg (fun r : ℝ => t ^ r) (by ring)
      _ = t ^ (3 : ℝ) * t ^ ((a - 1) * (2 : ℝ)) := Real.rpow_add ht _ _
      _ = t ^ 3 * (t ^ (a - 1)) ^ 2 := by
        have h2 : t ^ ((a - 1) * (2 : ℝ)) = (t ^ (a - 1)) ^ 2 :=
          Real.rpow_mul_natCast ht.le (a - 1) 2
        rw [Real.rpow_ofNat, h2]
  rw [rawPowerZero_reciprocal a t _ ht.ne' hh.ne', ← hrec,
    rawPowerOne_actual a (div_pos zero_lt_one ht) hr]
  unfold reciprocalPowerCertificate
  rw [hweight]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem spectralLeadingRatio_factorized (a t h theta : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 1)
    (hA : t + (1 - t) * theta ≠ 0) (hB : 1 - (1 - t) * theta ≠ 0) :
    spectralLeadingRatio a t h theta =
      2 * theta ^ 2 * (1 - theta) ^ 2 *
        ((1 - theta) * rawPowerZero a t h + theta * rawPowerOne a t h) /
          (a * (t + (1 - t) * theta) * (1 - (1 - t) * theta)) := by
  have hd : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  unfold spectralLeadingRatio rawPowerZero rawPowerOne
  generalize hAA : t + (1 - t) * theta = AA at *
  generalize hBB : 1 - (1 - t) * theta = BB at *
  generalize hDD : 1 - t = DD at *
  field_simp [ha, hd, hA, hB]
  rw [← hAA, ← hBB, ← hDD]
  ring

theorem spectralLeading_negative {a t theta c : ℝ}
    (ha : 1 < a ∨ a ≤ -2) (ht : 0 < t) (ht1 : t < 1)
    (hth0 : 0 < theta) (hth1 : theta < 1) (hca : 0 < c / a) :
    c * spectralLeadingRatio a t (t ^ (a - 1)) theta < 0 := by
  have han : a ≠ 0 := by rcases ha with hu | hl <;> linarith
  have hA : 0 < t + (1 - t) * theta := by positivity
  have hB : 0 < 1 - (1 - t) * theta := by
    have hid : 1 - (1 - t) * theta = (1 - theta) + t * theta := by ring
    rw [hid]
    positivity
  rw [spectralLeadingRatio_factorized _ _ _ _ han (ne_of_lt ht1) hA.ne' hB.ne',
    rawPowerZero_actual a ht (ne_of_lt ht1), rawPowerOne_actual a ht (ne_of_lt ht1)]
  have hfactor : 0 < (c / a) *
      (2 * theta ^ 2 * (1 - theta) ^ 2 /
        ((t + (1 - t) * theta) * (1 - (1 - t) * theta))) := by
    have hs0 := sq_pos_of_pos hth0
    have hs1 := sq_pos_of_pos (sub_pos.mpr hth1)
    positivity
  have hsum := weightedPowerCertificates_negative ha ht (ne_of_lt ht1) hth0 hth1
  have hprod := mul_neg_of_pos_of_neg hfactor hsum
  convert hprod using 1
  field_simp [han, hA.ne', hB.ne']

end

end ResearchMain.DiagonalSchatten
