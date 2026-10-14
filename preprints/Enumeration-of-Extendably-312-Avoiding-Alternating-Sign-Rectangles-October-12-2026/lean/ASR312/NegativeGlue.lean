import ASR312.BoundaryLines

namespace ASR312

 def negativeGlue {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1)) :
    Rectangle ((a+1)+(b+1)) ((a+1)+(b+1)) :=
  Fin.append
    (fun i => Fin.append (Fin.cons .zero (fun j => A i j.castSucc))
      (Fin.cons (A i (Fin.last a)) (fun _ : Fin b => .zero)))
    (Fin.cons
      (Fin.append (Fin.cons .plus (fun _ : Fin a => .zero))
        (Fin.cons .minus (fun j => B 0 j.succ)))
      (fun i => Fin.append (fun _ : Fin (a+1) => .zero) (B i.succ)))

 theorem negativeGlue_row_top {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1))
    (i : Fin (a+1)) : nonzeroEntries (row (negativeGlue A B) (i.castAdd (b+1))) =
      nonzeroEntries (row A i) := by
  conv_rhs => rw [row,List.ofFn_succ']
  simp only [row,negativeGlue,Fin.append_left]
  rw [List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_succ,List.ofFn_const,List.concat_eq_append]
  cases A i (Fin.last a) <;> simp

 theorem negativeGlue_row_bottom {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1))
    (i : Fin b) : nonzeroEntries (row (negativeGlue A B) (i.succ.natAdd (a+1))) =
      nonzeroEntries (row B i.succ) := by
  simp only [row,negativeGlue,Fin.append_right,Fin.cons_succ]
  rw [List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_const]

 theorem negativeGlue_row_pivot {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1))
    (hB : IsASM B) (hz : B 0 0 = .zero) :
    nonzeroEntries (row (negativeGlue A B) ((0 : Fin (b+1)).natAdd (a+1))) = [.plus,.minus,.plus] := by
  have hh := asm_first_row_tail_entries B hB hz
  simp only [nonzeroEntries] at hh
  simp only [row,negativeGlue,Fin.append_right,Fin.cons_zero]
  rw [List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_succ,List.ofFn_const,hh]

 theorem negativeGlue_col_zero {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1)) :
    nonzeroEntries (col (negativeGlue A B) ((0 : Fin (a+1)).castAdd (b+1))) = [.plus] := by
  have hf : (fun i => negativeGlue A B i ((0 : Fin (a+1)).castAdd (b+1))) =
      Fin.append (fun _ : Fin (a+1) => Entry.zero) (Fin.cons .plus (fun _ : Fin b => .zero)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [negativeGlue]
    · refine Fin.cases ?_ (fun i => ?_) i <;> simp [negativeGlue]
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_succ,List.ofFn_const]

 theorem negativeGlue_col_left {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1))
    (j : Fin a) : nonzeroEntries (col (negativeGlue A B) (j.succ.castAdd (b+1))) =
      nonzeroEntries (col A j.castSucc) := by
  have hf : (fun i => negativeGlue A B i (j.succ.castAdd (b+1))) =
      Fin.append (fun i => A i j.castSucc) (fun _ : Fin (b+1) => Entry.zero) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [negativeGlue]
    · refine Fin.cases ?_ (fun i => ?_) i <;> simp [negativeGlue]
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [col,List.ofFn_const]

 theorem negativeGlue_col_right {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1))
    (j : Fin b) : nonzeroEntries (col (negativeGlue A B) (j.succ.natAdd (a+1))) =
      nonzeroEntries (col B j.succ) := by
  have hf : (fun i => negativeGlue A B i (j.succ.natAdd (a+1))) =
      Fin.append (fun _ : Fin (a+1) => Entry.zero) (fun i => B i j.succ) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [negativeGlue]
    · refine Fin.cases ?_ (fun i => ?_) i <;> simp [negativeGlue]
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [col,List.ofFn_const]

 theorem negativeGlue_col_overlap {a b : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (b+1) (b+1))
    (hB : IsASM B) (hz : B 0 0 = .zero) :
    nonzeroEntries (col (negativeGlue A B) ((0 : Fin (b+1)).natAdd (a+1))) =
      nonzeroEntries (col A (Fin.last a)) ++ [.minus,.plus] := by
  have hf : (fun i => negativeGlue A B i ((0 : Fin (b+1)).natAdd (a+1))) =
      Fin.append (fun i => A i (Fin.last a)) (Fin.cons .minus (fun i : Fin b => B i.succ 0)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [negativeGlue]
    · refine Fin.cases ?_ (fun i => ?_) i <;> simp [negativeGlue]
  have hh := asm_first_col_tail_entries B hB hz
  simp only [nonzeroEntries] at hh
  rw [col,hf,List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [col,List.ofFn_succ,hh]

end ASR312
