import TerminalLogConcavity.ScaledBlock
import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace TerminalLogConcavity

theorem Block.scaled_d_ge (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    amplifier t ≤ (scaled t p).d := by
  have h : amplifier t ^ 1 ≤ amplifier t ^ p := Nat.pow_le_pow_right (amplifier_pos t) hp
  simpa using h.trans (scaled_d_lower t hp)

theorem one_add_le_entropy_mul {a d : ℝ} (ha : 0 < a) (had : a ≤ d) :
    1 + d ≤ d * (1 + 1 / a) := by
  have hdiv : 1 ≤ d / a := (le_div_iff₀ ha).mpr (by simpa using had)
  calc
    1 + d ≤ d / a + d := by linarith
    _ = _ := by ring

theorem Block.scaled_d_upper (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ((scaled t p).d : ℝ) ≤
      (amplifier t : ℝ) ^ p * (1 + 1 / (amplifier t : ℝ)) ^ (2 * (p - 1)) := by
  have ha : 0 < (amplifier t : ℝ) := by exact_mod_cast amplifier_pos t
  have hu : 0 ≤ 1 + 1 / (amplifier t : ℝ) := by positivity
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases he : p = 1
    · subst p; simp
    · have hp2 : 2 ≤ p := by omega
      have hlpos : 1 ≤ p / 2 := by omega
      have hrpos : 1 ≤ (p + 1) / 2 := by omega
      have hl := ih (p / 2) (by omega) hlpos
      have hr := ih ((p + 1) / 2) (by omega) hrpos
      have hdl : (amplifier t : ℝ) ≤ (scaled t (p / 2)).d := by
        exact_mod_cast scaled_d_ge t hlpos
      have hdr : (amplifier t : ℝ) ≤ (scaled t ((p + 1) / 2)).d := by
        exact_mod_cast scaled_d_ge t hrpos
      have h1 := one_add_le_entropy_mul ha hdl
      have h2 := one_add_le_entropy_mul ha hdr
      have hfirst := mul_le_mul h1 h2 (by positivity) (by positivity)
      have hprod := mul_le_mul hl hr (by positivity) (by positivity)
      have hlast := mul_le_mul_of_nonneg_right hprod
        (sq_nonneg (1 + 1 / (amplifier t : ℝ)))
      have hsplit : p / 2 + (p + 1) / 2 = p := by omega
      have hexp : 2 * (p / 2 - 1) + 2 * ((p + 1) / 2 - 1) + 2 = 2 * (p - 1) := by omega
      have hpow :
          ((amplifier t : ℝ) ^ (p / 2) *
              (1 + 1 / (amplifier t : ℝ)) ^ (2 * (p / 2 - 1))) *
          ((amplifier t : ℝ) ^ ((p + 1) / 2) *
              (1 + 1 / (amplifier t : ℝ)) ^ (2 * ((p + 1) / 2 - 1))) *
          (1 + 1 / (amplifier t : ℝ)) ^ 2 =
          (amplifier t : ℝ) ^ p * (1 + 1 / (amplifier t : ℝ)) ^ (2 * (p - 1)) := by
        conv_rhs => lhs; rw [← hsplit, pow_add]
        conv_rhs => rhs; rw [← hexp, pow_add, pow_add]
        ring
      rw [scaled_binary t hp2, d_binary]
      push_cast
      rw [← hpow]
      nlinarith

theorem Block.scaled_d_upper_exp (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    ((scaled t p).d : ℝ) ≤
      (amplifier t : ℝ) ^ p * Real.exp (2 * (p : ℝ) / amplifier t) := by
  have ha : 0 < (amplifier t : ℝ) := by exact_mod_cast amplifier_pos t
  have hbase : 1 + 1 / (amplifier t : ℝ) ≤ Real.exp (1 / (amplifier t : ℝ)) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / (amplifier t : ℝ))
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 1 / (amplifier t : ℝ))
    hbase (2 * (p - 1))
  rw [← Real.exp_nat_mul] at hpow
  have hexp : Real.exp ((2 * (p - 1) : ℕ) * (1 / (amplifier t : ℝ))) ≤
      Real.exp (2 * (p : ℝ) / amplifier t) := by
    apply Real.exp_le_exp.mpr
    have hn : ((2 * (p - 1) : ℕ) : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast (by omega : 2 * (p - 1) ≤ 2 * p)
    have hh := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 1 / (amplifier t : ℝ))
    simpa [div_eq_mul_inv] using hh
  exact (scaled_d_upper t hp).trans
    (mul_le_mul_of_nonneg_left (hpow.trans hexp) (by positivity))

theorem exp_le_two_of_le_half {x : ℝ} (hx : 0 ≤ x) (hh : x ≤ 1 / 2) :
    Real.exp x ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval hx (by linarith)
  exact h.trans ((div_le_iff₀ (by linarith : 0 < 1 - x)).mpr (by linarith))

theorem Block.scaled_d_le_twice_power (t : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (hsmall : 4 * p ≤ amplifier t) :
    ((scaled t p).d : ℝ) ≤ 2 * (amplifier t : ℝ) ^ p := by
  have ha : 0 < (amplifier t : ℝ) := by exact_mod_cast amplifier_pos t
  have hs : 4 * (p : ℝ) ≤ amplifier t := by exact_mod_cast hsmall
  have hexp := exp_le_two_of_le_half (by positivity : 0 ≤ 2 * (p : ℝ) / amplifier t)
    ((div_le_iff₀ ha).mpr (by linarith))
  have hm := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ (amplifier t : ℝ) ^ p)
  exact (scaled_d_upper_exp t hp).trans (by simpa [mul_comm] using hm)

end TerminalLogConcavity
