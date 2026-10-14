import ASR312.EnumerationSeriesRecurrence

namespace ASR312

open PowerSeries

theorem T_width_solution (a b : ℕ) :
    T a b = P*U a + R^b*(T a 0-P*U a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [T_width_recurrence,ih,pow_succ]
    have hh := P_sub_RP
    linear_combination -(U a)*hh

theorem T_row_complete (b : ℕ) : T 0 b = P*(1+R^b) := by
  rw [T_width_solution,U_zero,mul_one,T_square,← two_mul_P]
  ring

end ASR312
