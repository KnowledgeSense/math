import TerminalLogConcavity.BlockEnvelope

namespace TerminalLogConcavity

def Block.scaled (t p : ℕ) : Block :=
  if p ≤ 1 then balanced t
  else .binary (scaled t (p / 2)) (scaled t ((p + 1) / 2))
termination_by p
decreasing_by all_goals omega

@[simp] theorem Block.scaled_one (t : ℕ) : scaled t 1 = balanced t := by
  rw [scaled]; simp

theorem Block.scaled_binary (t : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    scaled t p = .binary (scaled t (p / 2)) (scaled t ((p + 1) / 2)) := by
  rw [scaled, ite_eq_right (by omega)]

theorem Block.scaled_rank (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    (scaled t p).rank + 1 = ((balanced t).rank + 1) * p := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases he : p = 1
    · subst p; simp
    · have hp2 : 2 ≤ p := by omega
      rw [scaled_binary t hp2, rank]
      have hl := ih (p / 2) (by omega) (by omega)
      have hr := ih ((p + 1) / 2) (by omega) (by omega)
      have hs : p / 2 + (p + 1) / 2 = p := by omega
      nlinarith

theorem Block.scaled_d_lower (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    amplifier t ^ p ≤ (scaled t p).d := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases he : p = 1
    · subst p; simp
    · have hp2 : 2 ≤ p := by omega
      rw [scaled_binary t hp2, d_binary]
      have hl := ih (p / 2) (by omega) (by omega)
      have hr := ih ((p + 1) / 2) (by omega) (by omega)
      have hs : p = p / 2 + (p + 1) / 2 := by omega
      conv_lhs => rw [hs, pow_add]
      exact (Nat.mul_le_mul hl hr).trans (by nlinarith)

theorem Block.balanced_rank (t : ℕ) : (balanced t).rank + 1 = 2 ^ (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [balanced, rank]; rw [pow_succ]; omega

theorem Block.scaled_rank_exact (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    (scaled t p).rank + 1 = 2 * 2 ^ t * p := by
  rw [scaled_rank t hp, balanced_rank, pow_succ]
  ring

end TerminalLogConcavity
