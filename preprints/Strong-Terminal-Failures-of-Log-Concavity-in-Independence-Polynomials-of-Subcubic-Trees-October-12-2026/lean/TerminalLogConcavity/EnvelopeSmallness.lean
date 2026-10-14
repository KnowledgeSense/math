import TerminalLogConcavity.SiteParameters

namespace TerminalLogConcavity

theorem selectedAmplifier_square_large {q H : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) :
    528 * q ^ 5 ≤ selectedAmplifier q H ^ 2 := by
  have ha := selectedAmplifier_ge_128 (by omega : 1 ≤ q) hH
  have hsq := Nat.pow_le_pow_left ha 2
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
  have hq5 : q ^ 5 ≤ q ^ 8 := by
    have h := Nat.mul_le_mul_left (q ^ 5) hq3
    simpa only [mul_one, ← pow_add] using h
  nlinarith

theorem release_envelope_small_nat {q H W : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hW : W ≤ 132 * q ^ 4 * selectedAmplifier q H ^ (massParameter q + q + 1)) :
    4 * q * W ≤ selectedAmplifier q H ^ (2 * massParameter q) := by
  let a := selectedAmplifier q H
  have ha : 0 < a := amplifier_pos _
  have hsq := selectedAmplifier_square_large hq hH
  have hstep := Nat.mul_le_mul_left (4 * q) hW
  have hmul := Nat.mul_le_mul_right (a ^ (massParameter q + q + 1)) hsq
  have hexp : 2 + (massParameter q + q + 1) ≤ 2 * massParameter q := by
    unfold massParameter
    nlinarith
  have hp := Nat.pow_le_pow_right ha hexp
  calc
    4 * q * W ≤ (528 * q ^ 5) * a ^ (massParameter q + q + 1) := by
      convert hstep using 1 ; dsimp [a] ; ring
    _ ≤ a ^ 2 * a ^ (massParameter q + q + 1) := hmul
    _ ≤ a ^ (2 * massParameter q) := by rw [← pow_add]; exact hp

theorem release_envelope_small {q H W : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hW : W ≤ 132 * q ^ 4 * selectedAmplifier q H ^ (massParameter q + q + 1)) :
    (W : ℝ) * ((q : ℝ) / (selectedAmplifier q H : ℝ) ^ (2 * massParameter q)) ≤ 1 / 4 := by
  have h := release_envelope_small_nat hq hH hW
  have hr : 4 * (q : ℝ) * W ≤ (selectedAmplifier q H : ℝ) ^ (2 * massParameter q) := by
    exact_mod_cast h
  have ha : 0 < (selectedAmplifier q H : ℝ) := by exact_mod_cast amplifier_pos (thresholdIndex (target q H))
  have hd : 0 < (selectedAmplifier q H : ℝ) ^ (2 * massParameter q) := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  nlinarith

end TerminalLogConcavity
