import MainTheorems.EulerianPencil.Sequence

namespace ResearchMain.EulerianPencil

open Polynomial

theorem oddF_pencil_splits (m : ℕ) (k : ℝ) :
    (oddF (m + 1) + C k * oddF m).Splits := by
  induction m with
  | zero =>
    norm_num [oddF, U, T]
    have hc : (C 6 : ℝ[X]) * C (-(1 + k) / 6) = -(1 + C k) := by
      rw [← map_one C, ← map_add, ← map_neg, ← map_mul]
      congr 1
      ring
    have h : (1 + C 6 * X : ℝ[X]) + C k = C 6 * (X - C (-(1 + k) / 6)) := by
      rw [mul_sub, hc]
      ring
    rw [h]
    exact (Splits.C _).mul (Splits.X_sub_C _)
  | succ m ih =>
    rw [oddF, show oddF (m + 1) = T (U (oddF m)) from rfl,
      ← T_C_mul, ← T_add, ← U_C_mul, ← U_add]
    exact T_preserves_splits (U_preserves_splits ih)

theorem evenF_pencil_splits (m : ℕ) (k : ℝ) :
    (evenF (m + 1) + C k * evenF m).Splits := by
  rw [evenF, evenF, ← U_C_mul, ← U_add]
  exact U_preserves_splits (oddF_pencil_splits m k)

end ResearchMain.EulerianPencil
