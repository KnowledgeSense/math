import MainTheorems.EulerianPencil.Lift

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def oddF : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => T (U (oddF m))

noncomputable def evenF (m : ℕ) : ℝ[X] := U (oddF m)

theorem U_degree_le {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) : (U f).natDegree ≤ m := by
  apply Polynomial.induction_with_natDegree_le (fun f => (U f).natDegree ≤ m) m
  · simp [U]
  · intro j a _ hj
    rw [U_C_mul, U_X_pow, ← map_natCast C]
    exact (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans
      (by simpa using hj))
  · intro f g _ _ ihf ihg
    rw [U_add]
    exact (natDegree_add_le _ _).trans (max_le ihf ihg)
  · exact hf

theorem T_degree_le {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) : (T f).natDegree ≤ m + 1 := by
  apply Polynomial.induction_with_natDegree_le (fun f => (T f).natDegree ≤ m + 1) m
  · simp [T]
  · intro j a _ hj
    rw [T_C_mul, T_X_pow, ← map_natCast C, ← map_natCast C]
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (by simpa using hj.trans (Nat.le_succ m))
    · exact (natDegree_C_mul_le _ _).trans (by simpa using Nat.succ_le_succ hj)
  · intro f g _ _ ihf ihg
    rw [T_add]
    exact (natDegree_add_le _ _).trans (max_le ihf ihg)
  · exact hf

theorem oddF_degree_le (m : ℕ) : (oddF m).natDegree ≤ m := by
  induction m with
  | zero => simp [oddF]
  | succ m ih => exact T_degree_le (U_degree_le ih)

theorem evenF_degree_le (m : ℕ) : (evenF m).natDegree ≤ m := U_degree_le (oddF_degree_le m)

theorem eulerianReal_recurrence (n : ℕ) :
    (eulerian (n + 1)).map (Int.castRingHom ℝ) =
      E n ((eulerian n).map (Int.castRingHom ℝ)) := by
  rw [eulerian_recurrence]
  simp [E, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, derivative_map]

theorem eulerian_lift (m : ℕ) :
    (eulerian (2 * m + 1)).map (Int.castRingHom ℝ) = lift m (oddF m) ∧
      (eulerian (2 * m + 2)).map (Int.castRingHom ℝ) = (1 + X) * lift m (evenF m) := by
  induction m with
  | zero =>
    constructor
    · simp [oddF, lift, eulerian_one]
    · rw [eulerianReal_recurrence 1, eulerian_one]
      simp [E, evenF, oddF, U, lift]
  | succ m ih =>
    have ho : (eulerian (2 * (m + 1) + 1)).map (Int.castRingHom ℝ) =
        lift (m + 1) (oddF (m + 1)) := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
        eulerianReal_recurrence, ih.2]
      simpa only [oddF, evenF, show 2 * m + 2 = 2 * (m + 1) by omega] using
        lift_T (evenF_degree_le m)
    refine ⟨ho, ?_⟩
    rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by omega,
      eulerianReal_recurrence, ho, lift_U (oddF_degree_le (m + 1))]
    rfl

theorem U_coeff (f : ℝ[X]) (k : ℕ) : (U f).coeff k = (k + 1 : ℝ) * f.coeff k := by
  cases k with
  | zero => simp [U]
  | succ k =>
    simp only [U, coeff_add, coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem T_constant (f : ℝ[X]) : (T f).coeff 0 = f.coeff 0 := by simp [T]

theorem T_coeff_succ (f : ℝ[X]) (k : ℕ) :
    (T f).coeff (k + 1) = (k + 2 : ℝ) * f.coeff (k + 1) + (4 * k + 6 : ℝ) * f.coeff k := by
  rw [T, show (1 + C 6 * X) * f + X * (1 + C 4 * X) * derivative f =
    f + C 6 * (X * f) + X * derivative f + C 4 * (X * (X * derivative f)) by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative]
  cases k with
  | zero => simp; ring
  | succ k =>
    simp only [coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem oddF_constant (m : ℕ) : (oddF m).coeff 0 = 1 := by
  induction m with
  | zero => simp [oddF]
  | succ m ih => simpa [oddF, T_constant, U_coeff] using ih

theorem evenF_constant (m : ℕ) : (evenF m).coeff 0 = 1 := by
  simpa [evenF, U_coeff] using oddF_constant m

theorem oddF_top_positive (m : ℕ) : 0 < (oddF m).coeff m := by
  induction m with
  | zero => simp [oddF]
  | succ m ih =>
    rw [oddF, T_coeff_succ, coeff_eq_zero_of_natDegree_lt
      (by have := U_degree_le (oddF_degree_le m); omega), mul_zero, zero_add, U_coeff]
    positivity

theorem evenF_top_positive (m : ℕ) : 0 < (evenF m).coeff m := by
  rw [evenF, U_coeff]
  exact mul_pos (by positivity) (oddF_top_positive m)

theorem oddF_natDegree (m : ℕ) : (oddF m).natDegree = m :=
  (oddF_degree_le m).antisymm (le_natDegree_of_ne_zero (oddF_top_positive m).ne')

theorem evenF_natDegree (m : ℕ) : (evenF m).natDegree = m :=
  (evenF_degree_le m).antisymm (le_natDegree_of_ne_zero (evenF_top_positive m).ne')

theorem oddF_splits (m : ℕ) : (oddF m).Splits := by
  induction m with
  | zero => simp [oddF]
  | succ m ih => exact T_preserves_splits (U_preserves_splits ih)

theorem evenF_splits (m : ℕ) : (evenF m).Splits := U_preserves_splits (oddF_splits m)

end ResearchMain.EulerianPencil
