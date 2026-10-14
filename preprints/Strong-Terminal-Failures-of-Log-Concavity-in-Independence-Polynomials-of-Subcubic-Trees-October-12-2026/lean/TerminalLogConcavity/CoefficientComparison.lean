import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Numerical transfer of the two-sided bounds to strict terminal failures. -/
namespace TerminalLogConcavity

theorem strict_failure_of_bounds
    {H B a cm c cp lm l lp : ℝ}
    (hH : 0 ≤ H) (hc : 0 ≤ c)
    (hlm : 0 ≤ lm) (hl : 0 < l) (hlp : 0 ≤ lp)
    (hm : lm ≤ cm) (hp : lp ≤ cp) (hu : c ≤ B * l)
    (hmodel : a ^ 2 * l ^ 2 ≤ 4 * (lm * lp))
    (hgap : 4 * H * B ^ 2 < a ^ 2) : H * c ^ 2 < cm * cp := by
  have hprod : lm * lp ≤ cm * cp :=
    mul_le_mul hm hp hlp (le_trans hlm hm)
  have hsq : c ^ 2 ≤ (B * l) ^ 2 := by nlinarith
  have hupper := mul_le_mul_of_nonneg_left hsq hH
  have hstrict := mul_lt_mul_of_pos_right hgap (sq_pos_of_pos hl)
  nlinarith

theorem adjacent_index_factor {q j : ℕ} (hj : 1 ≤ j) (hjq : j < q) :
    ((j + 1 : ℕ) : ℝ) * ((q - j + 1 : ℕ) : ℝ) ≤
      4 * (j : ℝ) * ((q - j : ℕ) : ℝ) := by
  have hdiff : 1 ≤ q - j := by omega
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hdr : (1 : ℝ) ≤ (q - j : ℕ) := by exact_mod_cast hdiff
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr hjr) (sub_nonneg.mpr hdr)]

end TerminalLogConcavity
