import GenericValueSemigroups.PivotColumn

namespace GenericValueSemigroups
open Matrix Finset

noncomputable def exponentialColumns {N q : ℕ} (a : Fin q → Fin N) (node : Fin q → ℝ) :
    Matrix (Fin N) (Fin q) ℝ := fun i j => exponentialMatrix N (node j) i (a j)

theorem exponentialColumns_factor {N q : ℕ} (a : Fin (q+1) → Fin N)
    (node : Fin (q+1) → ℝ) :
    exponentialColumns a node = exponentialMatrix N (node 0) *
      pivotColumn (a 0) (exponentialColumns (fun j => a j.succ) (fun j => node j.succ-node 0)) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [exponentialColumns, Matrix.mul_apply, pivotColumn, Fin.cases_zero]
    rw [Finset.sum_eq_single (a 0)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · change exponentialMatrix N (node j.succ) i (a j.succ) = _
    have he := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M i (a j.succ))
      (exponentialMatrix_add N (node 0) (node j.succ-node 0))
    simpa only [add_sub_cancel, Matrix.mul_apply, pivotColumn, Fin.cases_succ,
      exponentialColumns] using he

/-- Ordered shifted exponential columns have nonnegative minors; all feasible minors are positive. -/
theorem exponentialColumns_minor {N q : ℕ} (a : Fin q → Fin N) (node : Fin q → ℝ)
    (ha : Monotone a) (hnode : StrictMono node) (hpos : ∀ j, 0 < node j)
    (rows : Fin q → Fin N) (hr : StrictMono rows) :
    0 ≤ ((exponentialColumns a node).submatrix rows id).det ∧
      ((∀ j, a j ≤ rows j) → 0 < ((exponentialColumns a node).submatrix rows id).det) := by
  induction q with
  | zero => simp
  | succ q ih =>
    let a' : Fin q → Fin N := fun j => a j.succ
    let node' : Fin q → ℝ := fun j => node j.succ-node 0
    let Y := exponentialColumns a' node'
    let B := pivotColumn (a 0) Y
    have ha' : Monotone a' := ha.comp Fin.strictMono_succ.monotone
    have hnode' : StrictMono node' := by
      intro i j hij
      exact sub_lt_sub_right (hnode (Fin.succ_lt_succ_iff.mpr hij)) _
    have hp' : ∀ j, 0 < node' j := by
      intro j
      exact sub_pos.mpr (hnode (Fin.succ_pos j))
    have hY : ∀ r : Fin q → Fin N, StrictMono r → 0 ≤ (Y.submatrix r id).det := by
      intro r h
      exact (ih a' node' ha' hnode' hp' r h).1
    have hYzero : ∀ i j, i < a 0 → Y i j = 0 := by
      intro i j hi
      have ha0 : a 0 ≤ a j.succ := ha (Fin.zero_le _)
      have hn : ¬a' j ≤ i := by dsimp [a']; exact not_le_of_gt (hi.trans_le ha0)
      simp [Y, exponentialColumns, exponentialMatrix, hn]
    have hB : ∀ r : Fin (q+1) → Fin N, StrictMono r → 0 ≤ (B.submatrix r id).det :=
      pivotColumn_det_nonneg (a 0) Y hY hYzero
    let A := (exponentialMatrix N (node 0)).submatrix rows id
    have hA : ∀ r : Fin (q+1) → Fin N, StrictMono r → 0 ≤ (A.submatrix id r).det := by
      intro r h
      simpa only [A, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
        exponentialMatrix_totallyNonneg (hpos 0).le hr h
    have hfactor : (exponentialColumns a node).submatrix rows id = A*B := by
      rw [exponentialColumns_factor]
      ext i j
      simp [A, B, Y, a', node', Matrix.mul_apply]
    rw [hfactor]
    constructor
    · exact det_rectangular_mul_nonneg A B hA hB
    · intro hfeasible
      let mid : Fin (q+1) → Fin N := Fin.cons (a 0) (fun j => rows j.succ)
      have hm : StrictMono mid := by
        intro i j hij
        obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim (lt_irrefl _ hij)
          · exact (hfeasible 0).trans_lt (hr (Fin.succ_pos j))
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim (Fin.not_lt_zero _ hij)
          · exact hr hij
      have hmid : ∀ i, mid i ≤ rows i := by
        intro i
        exact Fin.cases (hfeasible 0) (fun _ => le_rfl) i
      have hea : 0 < (A.submatrix id mid).det := by
        simpa only [A, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using
          exponentialMatrix_minor_pos (hpos 0) rows mid hr hm hmid
      have heb : 0 < (B.submatrix mid id).det := by
        rw [pivotColumn_det_eq (a 0) Y mid hm (by rfl)]
        exact (ih a' node' ha' hnode' hp' (fun j => rows j.succ)
          (hr.comp Fin.strictMono_succ)).2 (fun j => hfeasible j.succ)
      exact det_rectangular_mul_pos A B hA hB mid hea heb

/-- The constant first column is separated from the positive-node minor. -/
theorem exponentialColumns_minor_zero_first {N q : ℕ}
    (a : Fin (q+1) → Fin N) (node : Fin (q+1) → ℝ)
    (ha : Monotone a) (hnode : StrictMono node) (hzero : node 0 = 0)
    (rows : Fin (q+1) → Fin N) (hr : StrictMono rows)
    (hfirst : rows 0 = a 0) (hle : ∀ j, a j ≤ rows j) :
    0 < ((exponentialColumns a node).submatrix rows id).det := by
  rw [exponentialColumns_factor, hzero, exponentialMatrix_zero, Matrix.one_mul]
  simp only [sub_zero]
  rw [pivotColumn_det_eq _ _ rows hr hfirst]
  apply (exponentialColumns_minor (fun j => a j.succ) (fun j => node j.succ)
    (ha.comp Fin.strictMono_succ.monotone) (hnode.comp Fin.strictMono_succ)
    (fun j => by simpa [hzero] using hnode (Fin.succ_pos j))
    (fun j => rows j.succ) (hr.comp Fin.strictMono_succ)).2
  exact fun j => hle j.succ

end GenericValueSemigroups
