import MainTheorems.DiagonalSchatten.DividedPowerUpper
import MainTheorems.DiagonalSchatten.DividedPowerLower

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem dividedPowerQuadratic_at_one (a : ℝ) :
    dividedPowerQuadratic a 1 (dividedPower a 1) = 0 := by
  have hz : dividedPower a 1 = a := by simp [dividedPower]
  rw [hz]
  unfold dividedPowerQuadratic
  ring

theorem dividedPowerQuadratic_positive_negative {a t : ℝ}
    (ha : a ≤ -2) (ht : 0 < t) (hneq : t ≠ 1) :
    0 < dividedPowerQuadratic a t (dividedPower a t) := by
  have h := negative_divided_power_quadratic_positive (m := -a) (by linarith) ht hneq
  rw [neg_neg] at h
  have hz : dividedPower a t = -((1 - t ^ a) / (t - 1)) := by
    simp only [dividedPower, ite_eq_right hneq]
    ring
  rw [hz]
  convert h using 1
  unfold dividedPowerQuadratic lowerPowerQuadratic
  ring

theorem dividedPowerQuadratic_nonneg {a t : ℝ}
    (ha : 1 < a ∨ a ≤ -2) (ht : 0 < t) :
    0 ≤ dividedPowerQuadratic a t (dividedPower a t) := by
  by_cases hneq : t = 1
  · subst t
    rw [dividedPowerQuadratic_at_one]
  · rcases ha with hu | hl
    · exact (dividedPowerQuadratic_positive hu ht hneq).le
    · exact (dividedPowerQuadratic_positive_negative hl ht hneq).le

def powerCertificate (a t : ℝ) : ℝ :=
  -(t - 1) ^ 2 * dividedPowerQuadratic a t (dividedPower a t)

def reciprocalPowerCertificate (a t : ℝ) : ℝ :=
  t ^ (2 * a + 1) * powerCertificate a (1 / t)

theorem powerCertificate_negative {a t : ℝ} (ha : 1 < a ∨ a ≤ -2)
    (ht : 0 < t) (hneq : t ≠ 1) : powerCertificate a t < 0 := by
  have hq : 0 < dividedPowerQuadratic a t (dividedPower a t) := by
    rcases ha with hu | hl
    · exact dividedPowerQuadratic_positive hu ht hneq
    · exact dividedPowerQuadratic_positive_negative hl ht hneq
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hneq))) hq

theorem reciprocalPowerCertificate_negative {a t : ℝ} (ha : 1 < a ∨ a ≤ -2)
    (ht : 0 < t) (hneq : t ≠ 1) : reciprocalPowerCertificate a t < 0 := by
  have hrec : 1 / t ≠ 1 := by
    intro h
    have ht1 := (div_eq_iff ht.ne').mp h
    exact hneq (by linarith)
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos ht _)
    (powerCertificate_negative ha (div_pos zero_lt_one ht) hrec)

theorem weightedPowerCertificates_negative {a t theta : ℝ}
    (ha : 1 < a ∨ a ≤ -2) (ht : 0 < t) (hneq : t ≠ 1)
    (hth0 : 0 < theta) (hth1 : theta < 1) :
    (1 - theta) * reciprocalPowerCertificate a t + theta * powerCertificate a t < 0 :=
  add_neg
    (mul_neg_of_pos_of_neg (sub_pos.mpr hth1) (reciprocalPowerCertificate_negative ha ht hneq))
    (mul_neg_of_pos_of_neg hth0 (powerCertificate_negative ha ht hneq))

end

end ResearchMain.DiagonalSchatten
