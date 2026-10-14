import TerminalLogConcavity.Amplifier
import TerminalLogConcavity.CoefficientComparison

namespace TerminalLogConcavity

def target (q H : ℕ) : ℕ := 2 ^ (q + 10) * q ^ 4 * H

noncomputable def selectedAmplifier (q H : ℕ) : ℕ :=
  amplifier (thresholdIndex (target q H))

theorem target_factorization (q H : ℕ) :
    target q H = 128 * 2 ^ (q + 3) * q ^ 4 * H := by
  unfold target
  have he : q + 10 = (q + 3) + 7 := by omega
  rw [he, pow_add]
  norm_num only [show (2 : ℕ) ^ 7 = 128 by decide]
  ring

theorem target_lower {q H : ℕ} (hq : 1 ≤ q) :
    128 * 2 ^ (q + 3) * H ≤ target q H := by
  rw [target_factorization]
  have hp : 1 ≤ q ^ 4 := Nat.one_le_pow 4 q (by omega)
  calc
    128 * 2 ^ (q + 3) * H = (128 * 2 ^ (q + 3) * 1) * H := by ring
    _ ≤ (128 * 2 ^ (q + 3) * q ^ 4) * H :=
      Nat.mul_le_mul_right H (Nat.mul_le_mul_left _ hp)

theorem target_gt_one {q H : ℕ} (hq : 1 ≤ q) (hH : 1 ≤ H) :
    1 < target q H := by
  have h := target_lower (H := H) hq
  have hp : 0 < 2 ^ (q + 3) := by positivity
  nlinarith

theorem selectedAmplifier_bounds {q H : ℕ} (hq : 1 ≤ q) (hH : 1 ≤ H) :
    target q H ≤ selectedAmplifier q H ∧
      selectedAmplifier q H ≤ target q H ^ 2 :=
  ⟨threshold_reached _, threshold_amplifier_le_square (target_gt_one hq hH)⟩

theorem selectedAmplifier_gap {q H : ℕ} (hq : 1 ≤ q) (hH : 1 ≤ H) :
    4 * (H : ℝ) * ((2 : ℝ) ^ (q + 3)) ^ 2 <
      (selectedAmplifier q H : ℝ) ^ 2 := by
  have hn := le_trans (target_lower (H := H) hq) (selectedAmplifier_bounds hq hH).1
  have hr : 128 * (2 : ℝ) ^ (q + 3) * (H : ℝ) ≤ selectedAmplifier q H := by
    exact_mod_cast hn
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hB : 0 < (2 : ℝ) ^ (q + 3) := by positivity
  have hBH : 0 < (2 : ℝ) ^ (q + 3) * H := by positivity
  have hHsq : (H : ℝ) ≤ (H : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hHsq (le_of_lt (sq_pos_of_pos hB))
  have hsquare : (128 * (2 : ℝ) ^ (q + 3) * H) ^ 2 ≤
      (selectedAmplifier q H : ℝ) ^ 2 := by nlinarith
  nlinarith [sq_pos_of_pos hBH]

theorem strict_failure_of_release_bounds {q H : ℕ} (hq : 1 ≤ q) (hH : 1 ≤ H)
    {cm c cp lm l lp : ℝ} (hc : 0 ≤ c) (hlm : 0 ≤ lm)
    (hl : 0 < l) (hlp : 0 ≤ lp)
    (hm : lm ≤ cm) (hp : lp ≤ cp) (hu : c ≤ (2 : ℝ) ^ (q + 3) * l)
    (hmodel : (selectedAmplifier q H : ℝ) ^ 2 * l ^ 2 ≤ 4 * (lm * lp)) :
    (H : ℝ) * c ^ 2 < cm * cp :=
  strict_failure_of_bounds (by positivity) hc hlm hl hlp hm hp hu hmodel
    (selectedAmplifier_gap hq hH)

end TerminalLogConcavity
