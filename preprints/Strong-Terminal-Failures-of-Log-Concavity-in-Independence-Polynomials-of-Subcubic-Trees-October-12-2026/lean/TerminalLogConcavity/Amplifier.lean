import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The numerical amplifier sequence in Lemma 3.4(i). -/
namespace TerminalLogConcavity

def amplifier : ℕ → ℕ
  | 0 => 1
  | t + 1 => (1 + amplifier t) ^ 2

@[simp] theorem amplifier_zero : amplifier 0 = 1 := rfl

@[simp] theorem amplifier_succ (t : ℕ) :
    amplifier (t + 1) = (1 + amplifier t) ^ 2 := rfl

theorem amplifier_pos (t : ℕ) : 0 < amplifier t := by
  induction t with
  | zero => decide
  | succ t ih => rw [amplifier_succ]; positivity

theorem amplifier_lt_succ (t : ℕ) : amplifier t < amplifier (t + 1) := by
  rw [amplifier_succ]
  nlinarith [amplifier_pos t]

theorem amplifier_strictMono : StrictMono amplifier :=
  strictMono_nat_of_lt_succ amplifier_lt_succ

theorem index_lt_amplifier (t : ℕ) : t < amplifier t := by
  induction t with
  | zero => decide
  | succ t ih => exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ ih) (amplifier_lt_succ t)

theorem amplifier_growth (t : ℕ) : 2 ^ (2 ^ (t + 1)) ≤ amplifier (t + 1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [amplifier_succ, pow_succ (2 : ℕ) (t + 1), pow_mul]
    exact Nat.pow_le_pow_left (by omega) 2

theorem exists_amplifier_ge (Q : ℕ) : ∃ t, Q ≤ amplifier t :=
  ⟨Q, Nat.le_of_lt (index_lt_amplifier Q)⟩

noncomputable def thresholdIndex (Q : ℕ) : ℕ := Nat.find (exists_amplifier_ge Q)

theorem threshold_reached (Q : ℕ) : Q ≤ amplifier (thresholdIndex Q) :=
  Nat.find_spec (exists_amplifier_ge Q)

theorem below_threshold {Q t : ℕ} (ht : t < thresholdIndex Q) : amplifier t < Q := by
  exact Nat.lt_of_not_ge (Nat.find_min (exists_amplifier_ge Q) ht)

theorem thresholdIndex_pos {Q : ℕ} (hQ : 1 < Q) : 0 < thresholdIndex Q := by
  have h := threshold_reached Q
  by_contra hn
  have hz : thresholdIndex Q = 0 := by omega
  rw [hz, amplifier_zero] at h
  omega

theorem threshold_amplifier_le_square {Q : ℕ} (hQ : 1 < Q) :
    amplifier (thresholdIndex Q) ≤ Q ^ 2 := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (thresholdIndex_pos hQ))
  have hb : amplifier t < Q := below_threshold (by omega)
  rw [ht, amplifier_succ]
  nlinarith

theorem amplifier_initial_values :
    amplifier 1 = 4 ∧ amplifier 2 = 25 ∧ amplifier 3 = 676 ∧
      amplifier 4 = 458329 := by decide

end TerminalLogConcavity
