import MainTheorems.EulerianPencil.RealRoots
import Mathlib.FieldTheory.Separable

namespace ResearchMain.EulerianPencil

open Polynomial

def SimpleRoots (f : ℝ[X]) : Prop := ∀ x : ℝ, f.eval x = 0 → (derivative f).eval x ≠ 0

theorem simpleRoots_of_separable {f : ℝ[X]} (hs : f.Separable) : SimpleRoots f := by
  intro x hx
  exact hs.eval₂_derivative_ne_zero (RingHom.id ℝ) (by simpa using hx)

theorem separable_of_simpleRoots {f : ℝ[X]} (hs : f.Splits) (hf : f ≠ 0)
    (hr : SimpleRoots f) : f.Separable := by
  rw [Separable, ← gcd_isUnit_iff, isUnit_iff_degree_eq_zero]
  by_contra hc
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero
    (Splits.of_dvd hs hf (gcd_dvd_left f (derivative f))) hc
  obtain ⟨a, ha⟩ := gcd_dvd_left f (derivative f)
  obtain ⟨b, hb⟩ := gcd_dvd_right f (derivative f)
  apply hr x (by rw [ha, eval_mul, hx, zero_mul])
  rw [hb, eval_mul, hx, zero_mul]

theorem U_simpleRoots {f : ℝ[X]} (h : f.Splits) (hs : SimpleRoots f) : SimpleRoots (U f) := by
  intro x hx hdx
  have hq : f.eval x + x * (derivative f).eval x = 0 := by simpa [U] using hx
  have hqd : 2 * (derivative f).eval x + x * (derivative (derivative f)).eval x = 0 := by
    have he := hdx
    simp [U, derivative_mul] at he
    linear_combination he
  have hf : f.eval x ≠ 0 := by
    intro he
    have hd := hs x he
    have hmul : x * (derivative f).eval x = 0 := by simpa [he] using hq
    have hx0 := (mul_eq_zero.mp hmul).resolve_right hd
    rw [hx0, zero_mul, add_zero] at hqd
    rw [hx0] at hd
    exact hd (by linarith)
  have hh : f.eval x ^ 2 + x ^ 2 * laguerre f x = 0 := by
    unfold laguerre
    linear_combination (f.eval x + x * (derivative f).eval x) * hq - x * f.eval x * hqd
  have hp := mul_nonneg (sq_nonneg x) (laguerre_nonnegative h x)
  have hf2 := sq_pos_of_ne_zero hf
  linarith

theorem T_simpleRoots {f : ℝ[X]} (h : f.Splits) (hs : SimpleRoots f) : SimpleRoots (T f) := by
  intro x hx hdx
  have hq : (1 + 6 * x) * f.eval x + x * (1 + 4 * x) * (derivative f).eval x = 0 := by
    simpa [T] using hx
  have hqd : 6 * f.eval x + (2 + 14 * x) * (derivative f).eval x +
      x * (1 + 4 * x) * (derivative (derivative f)).eval x = 0 := by
    have he := hdx
    simp [T, derivative_mul, derivative_add] at he
    linear_combination he
  have hf : f.eval x ≠ 0 := by
    intro he
    have hd := hs x he
    have hmul : x * (1 + 4 * x) * (derivative f).eval x = 0 := by simpa [he] using hq
    have hv := (mul_eq_zero.mp hmul).resolve_right hd
    rw [he, mul_zero, hv, zero_mul, zero_add, add_zero] at hqd
    rcases mul_eq_zero.mp hv with hx0 | hx4
    · rw [hx0] at hqd hd
      exact hd (by linarith)
    · have hx4' : x = -(1 / 4 : ℝ) := by linarith
      rw [hx4'] at hqd hd
      exact hd (by linarith)
  have hh : (1 + 8 * x + 24 * x ^ 2) * f.eval x ^ 2 +
      (x * (1 + 4 * x)) ^ 2 * laguerre f x = 0 := by
    unfold laguerre
    linear_combination ((1 + 8 * x) * f.eval x + x * (1 + 4 * x) *
      (derivative f).eval x) * hq - x * (1 + 4 * x) * f.eval x * hqd
  have hc : 0 < 1 + 8 * x + 24 * x ^ 2 := by nlinarith [sq_nonneg (x + 1 / 6)]
  have hp := mul_nonneg (sq_nonneg (x * (1 + 4 * x))) (laguerre_nonnegative h x)
  have hf2 := mul_pos hc (sq_pos_of_ne_zero hf)
  linarith

theorem oddF_simpleRoots (m : ℕ) : SimpleRoots (oddF m) := by
  induction m with
  | zero => simp [oddF, SimpleRoots]
  | succ m ih =>
    exact T_simpleRoots (evenF_splits m) (U_simpleRoots (oddF_splits m) ih)

theorem evenF_simpleRoots (m : ℕ) : SimpleRoots (evenF m) :=
  U_simpleRoots (oddF_splits m) (oddF_simpleRoots m)

theorem oddF_separable (m : ℕ) : (oddF m).Separable :=
  separable_of_simpleRoots (oddF_splits m) (oddF_rootInterval m).1 (oddF_simpleRoots m)

theorem evenF_separable (m : ℕ) : (evenF m).Separable :=
  separable_of_simpleRoots (evenF_splits m) (evenF_rootInterval m).1 (evenF_simpleRoots m)

theorem oddF_pencil_simpleRoots (m : ℕ) (k : ℝ) :
    SimpleRoots (oddF (m + 1) + C k * oddF m) := by
  induction m with
  | zero =>
    intro x _
    norm_num [oddF, U, T, derivative_mul]
  | succ m ih =>
    rw [oddF, show oddF (m + 1) = T (U (oddF m)) from rfl,
      ← T_C_mul, ← T_add, ← U_C_mul, ← U_add]
    exact T_simpleRoots (U_preserves_splits (oddF_pencil_splits m k))
      (U_simpleRoots (oddF_pencil_splits m k) ih)

theorem evenF_pencil_simpleRoots (m : ℕ) (k : ℝ) :
    SimpleRoots (evenF (m + 1) + C k * evenF m) := by
  rw [evenF, evenF, ← U_C_mul, ← U_add]
  exact U_simpleRoots (oddF_pencil_splits m k) (oddF_pencil_simpleRoots m k)

end ResearchMain.EulerianPencil
