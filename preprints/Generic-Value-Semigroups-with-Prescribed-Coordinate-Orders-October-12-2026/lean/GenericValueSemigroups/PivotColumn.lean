import GenericValueSemigroups.Toeplitz

namespace GenericValueSemigroups
open Matrix Finset

noncomputable def pivotColumn {N q : ℕ} (a : Fin N) (Y : Matrix (Fin N) (Fin q) ℝ) :
    Matrix (Fin N) (Fin (q+1)) ℝ :=
  fun i j => Fin.cases (if i=a then 1 else 0) (fun j => Y i j) j

theorem pivotColumn_det_eq {N q : ℕ} (a : Fin N) (Y : Matrix (Fin N) (Fin q) ℝ)
    (rows : Fin (q+1) → Fin N) (hr : StrictMono rows) (he : rows 0 = a) :
    ((pivotColumn a Y).submatrix rows id).det =
      (Y.submatrix (fun i => rows i.succ) id).det := by
  classical
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (0 : Fin (q+1))]
  · simp only [Matrix.submatrix_apply, id_eq, pivotColumn, Fin.cases_zero, he,
      ite_true, Fin.val_zero, pow_zero, mul_one, one_mul, Fin.succAbove_zero,
      Matrix.submatrix_submatrix]
    congr 1
  · intro i _ hi
    have hne : rows i ≠ a := by rw [← he]; exact fun h => hi (hr.injective h)
    simp [pivotColumn, hne]
  · simp

theorem pivotColumn_det_nonneg {N q : ℕ} (a : Fin N) (Y : Matrix (Fin N) (Fin q) ℝ)
    (hY : ∀ rows : Fin q → Fin N, StrictMono rows → 0 ≤ (Y.submatrix rows id).det)
    (hz : ∀ i j, i < a → Y i j = 0)
    (rows : Fin (q+1) → Fin N) (hr : StrictMono rows) :
    0 ≤ ((pivotColumn a Y).submatrix rows id).det := by
  classical
  rcases lt_trichotomy (rows 0) a with h | he | h
  · have hzero : ((pivotColumn a Y).submatrix rows id).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero 0
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [pivotColumn, ne_of_lt h]
      · exact hz _ j h
    rw [hzero]
  · rw [pivotColumn_det_eq a Y rows hr he]
    exact hY _ (hr.comp Fin.strictMono_succ)
  · have hzero : ((pivotColumn a Y).submatrix rows id).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro i
      have hne : rows i ≠ a := ne_of_gt (h.trans_le (hr.monotone (Fin.zero_le i)))
      simp [pivotColumn, hne]
    rw [hzero]

end GenericValueSemigroups
