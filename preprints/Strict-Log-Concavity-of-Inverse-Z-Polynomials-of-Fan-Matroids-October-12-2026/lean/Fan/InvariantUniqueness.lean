import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace Fan
open Polynomial

theorem low_support_symmetric_zero {R : Type*} [Ring R] (p : Polynomial R) (n : ℕ)
    (hlow : ∀ j, n ≤ 2 * j → p.coeff j = 0)
    (hsymm : ∀ j, j ≤ n → p.coeff j = p.coeff (n - j)) : p = 0 := by
  ext j
  rw [coeff_zero]
  by_cases hj : n ≤ 2 * j
  · exact hlow j hj
  · rw [hsymm j (by omega)]
    exact hlow _ (by omega)

theorem renewal_coefficient {R : Type*} [CommRing R]
    (B t : R) (Q Y : PowerSeries R)
    (h : (1 - PowerSeries.C B * PowerSeries.X - PowerSeries.C t * PowerSeries.X * Q) * Y =
      (1 - PowerSeries.C B * PowerSeries.X) * Q) (n : ℕ) :
    PowerSeries.coeff (n + 1) Y - PowerSeries.coeff (n + 1) Q =
      B * (PowerSeries.coeff n Y - PowerSeries.coeff n Q) +
      t * PowerSeries.coeff n (Q * Y) := by
  have he : Y - Q = PowerSeries.X *
      (PowerSeries.C B * (Y - Q) + PowerSeries.C t * (Q * Y)) := by
    linear_combination h
  have hc := congrArg (PowerSeries.coeff (n + 1)) he
  simpa only [map_sub, PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_C_mul] using hc

/-- The original renewal equation, low support and rank symmetry determine both sequences. -/
theorem coupled_renewal_unique {R : Type*} [CommRing R]
    (B t : Polynomial R) (Q Y Q' Y' : PowerSeries (Polynomial R))
    (hQ0 : PowerSeries.coeff 0 Q = PowerSeries.coeff 0 Q')
    (hY0 : PowerSeries.coeff 0 Y = PowerSeries.coeff 0 Y')
    (hQ : ∀ n, 0 < n → ∀ j, n ≤ 2 * j → (PowerSeries.coeff n Q).coeff j = 0)
    (hQ' : ∀ n, 0 < n → ∀ j, n ≤ 2 * j → (PowerSeries.coeff n Q').coeff j = 0)
    (hY : ∀ n j, j ≤ n → (PowerSeries.coeff n Y).coeff j =
      (PowerSeries.coeff n Y).coeff (n - j))
    (hY' : ∀ n j, j ≤ n → (PowerSeries.coeff n Y').coeff j =
      (PowerSeries.coeff n Y').coeff (n - j))
    (he : (1 - PowerSeries.C B * PowerSeries.X - PowerSeries.C t * PowerSeries.X * Q) * Y =
      (1 - PowerSeries.C B * PowerSeries.X) * Q)
    (he' : (1 - PowerSeries.C B * PowerSeries.X - PowerSeries.C t * PowerSeries.X * Q') * Y' =
      (1 - PowerSeries.C B * PowerSeries.X) * Q') : Q = Q' ∧ Y = Y' := by
  have hall : ∀ n, PowerSeries.coeff n Q = PowerSeries.coeff n Q' ∧
      PowerSeries.coeff n Y = PowerSeries.coeff n Y' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => exact ⟨hQ0, hY0⟩
      | succ m =>
        have hprod : PowerSeries.coeff m (Q * Y) = PowerSeries.coeff m (Q' * Y') := by
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          apply Finset.sum_congr rfl
          rintro ⟨i, j⟩ hij
          have hij' := Finset.mem_antidiagonal.mp hij
          rw [(ih i (by omega)).1, (ih j (by omega)).2]
        have hd : PowerSeries.coeff (m + 1) Y - PowerSeries.coeff (m + 1) Y' =
            PowerSeries.coeff (m + 1) Q - PowerSeries.coeff (m + 1) Q' := by
          have ha := renewal_coefficient B t Q Y he m
          have hb := renewal_coefficient B t Q' Y' he' m
          rw [(ih m (by omega)).1, (ih m (by omega)).2, hprod] at ha
          linear_combination ha - hb
        have hzero : PowerSeries.coeff (m + 1) Q - PowerSeries.coeff (m + 1) Q' = 0 := by
          apply low_support_symmetric_zero _ (m + 1)
          · intro j hj
            simp only [coeff_sub, hQ _ (by omega) j hj, hQ' _ (by omega) j hj, sub_self]
          · intro j hj
            rw [← hd, coeff_sub, coeff_sub, hY _ _ hj, hY' _ _ hj]
        exact ⟨sub_eq_zero.mp hzero, sub_eq_zero.mp (hd.trans hzero)⟩
  exact ⟨PowerSeries.ext (fun n => (hall n).1), PowerSeries.ext (fun n => (hall n).2)⟩

end Fan
