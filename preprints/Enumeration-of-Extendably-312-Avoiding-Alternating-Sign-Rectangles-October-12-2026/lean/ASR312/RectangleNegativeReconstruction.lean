import ASR312.RectangleNegativeExtraction

namespace ASR312

theorem rectangle_firstColumn_other_zero {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (p : Fin r) (hp : A p 0 = .plus) (q : Fin r) (hqp : q ≠ p) : A q 0 = .zero := by
  have hm := firstColumn_not_minus A ha q
  have hn : A q 0 ≠ .plus := fun h => hqp (firstColumn_plus_unique A ha h hp)
  cases hx : A q 0 <;> simp_all

theorem rectangle_negative_pivot_left_zero {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (p : Fin r) (z : Fin (k+1))
    (hp : A p 0 = .plus) (hm : A p z = .minus) (j : Fin (k+1)) (hj0 : j ≠ 0) (hjz : j < z) :
    A p j = .zero := by
  rcases row_firstColumn_structure A ha he p hp with hh | ⟨u,v,_,huv,hu,_,hh⟩
  · rw [hh z (by intro h; subst z; rw [hp] at hm; cases hm)] at hm
    cases hm
  · have huz := rectangle_negative_pivot_diagonal A he p u hp hu
    have hzz := rectangle_negative_pivot_diagonal A he p z hp hm
    have heq : u = z := Fin.ext (huz.symm.trans hzz)
    subst u
    exact hh j hj0 (ne_of_lt hjz) (ne_of_lt (lt_trans hjz huv))

theorem rectangle_negative_reconstruction {a r k : ℕ}
    (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) (ha : IsASR A) (he : ExtendablyAvoids312 A)
    (hp : A ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus)
    (hm : A ((0 : Fin (r+1)).natAdd (a+1)) ((0 : Fin (k+1)).natAdd (a+1)) = .minus) :
    rectangleNegativeGlue (rectangleNegativeTop A) (rectangleNegativeBottom A) = A := by
  funext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [rectangleNegativeGlue,Fin.append_left,Fin.cons_zero]
        exact (rectangle_firstColumn_other_zero A ha _ hp _ (by apply Fin.ne_of_val_ne; change i.val ≠ a+1; omega)).symm
      · simp only [rectangleNegativeGlue,rectangleNegativeTop,Fin.append_left,Fin.cons_succ]
        congr 1
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [rectangleNegativeGlue,rectangleNegativeTop,Fin.append_left,Fin.append_right,Fin.cons_zero]
        congr 1
      · simp only [rectangleNegativeGlue,Fin.append_left,Fin.append_right,Fin.cons_succ]
        exact (rectangle_pivot_top_right_zero A he _ hp _ _
          (by change i.val < a+1; omega) (by change a+1 < a+1+(j.val+1); omega)).symm
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [rectangleNegativeGlue,Fin.append_right,Fin.cons_zero,Fin.append_left]
          change Entry.plus = A ((0 : Fin (r+1)).natAdd (a+1)) 0
          exact hp.symm
        · simp only [rectangleNegativeGlue,Fin.append_right,Fin.cons_zero,Fin.append_left,Fin.cons_succ]
          exact (rectangle_negative_pivot_left_zero A ha he _ _ hp hm _
            (by apply Fin.ne_of_val_ne; simp) (by change j.val+1 < a+1; omega)).symm
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa [rectangleNegativeGlue] using hm.symm
        · simp [rectangleNegativeGlue,rectangleNegativeBottom]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [rectangleNegativeGlue,Fin.append_right,Fin.cons_succ,Fin.append_left]
        exact (rectangle_pivot_below_left_zero A he _ hp _ _
          (by change a+1 < a+1+(i.val+1); omega) (by change j.val < a+1; omega)).symm
      · simp [rectangleNegativeGlue,rectangleNegativeBottom]

theorem rectangleNegativeGlue_top {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) : rectangleNegativeTop (rectangleNegativeGlue A B) = A := by
  funext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hj : (⟨(Fin.last a).val+1,by omega⟩ : Fin ((a+1)+(k+1))) =
        (0 : Fin (k+1)).natAdd (a+1) := Fin.ext (by simp)
    simp only [rectangleNegativeTop,hj,rectangleNegativeGlue,Fin.append_left,Fin.append_right,Fin.cons_zero]
  · have hj : (⟨j.castSucc.val+1,by omega⟩ : Fin ((a+1)+(k+1))) = j.succ.castAdd (k+1) := Fin.ext rfl
    simp only [rectangleNegativeTop,hj,rectangleNegativeGlue,Fin.append_left,Fin.cons_succ]

theorem rectangleNegativeGlue_bottom {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (hz : B 0 0 = .zero) :
    rectangleNegativeBottom (rectangleNegativeGlue A B) = B := by
  funext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [rectangleNegativeBottom,rectangleNegativeGlue,hz]
  · simp [rectangleNegativeBottom,rectangleNegativeGlue]

theorem rectangleNegativeGlue_nonemptyRows {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (ha : IsASM A) (hav : Avoids312 A)
    (hb : IsASR B) (he : ExtendablyAvoids312 B) (hn : ∃ j, B 0 j ≠ .zero)
    (hz : B 0 0 = .zero) : nonemptyRows (rectangleNegativeGlue A B) = a+1+nonemptyRows B := by
  have ht := total_sum_nonemptyRows _ (rectangleNegativeGlue_asr A B ha hav hb he hn hz)
  have htop (i : Fin (a+1)) : (∑ j, (rectangleNegativeGlue A B (i.castAdd (r+1)) j).value) =
      ∑ j, (A i j).value := by
    rw [← row_entrySum,← nonzeroEntries_sum,rectangleNegativeGlue_row_top,nonzeroEntries_sum,row_entrySum]
  have hbot (i : Fin (r+1)) : (∑ j, (rectangleNegativeGlue A B (i.natAdd (a+1)) j).value) =
      ∑ j, (B i j).value := by
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [← row_entrySum,← nonzeroEntries_sum,rectangleNegativeGlue_row_pivot A B hb hn hz]
      conv_rhs => rw [← row_entrySum,← nonzeroEntries_sum,asr_firstRow_entries B hb hn]
      norm_num [entrySum,Entry.value]
    · rw [← row_entrySum,← nonzeroEntries_sum,rectangleNegativeGlue_row_bottom,nonzeroEntries_sum,row_entrySum]
  rw [Fin.sum_univ_add] at ht
  simp_rw [htop,hbot] at ht
  rw [total_sum_nonemptyRows A ha.1,total_sum_nonemptyRows B hb,
    (nonemptyRows_eq_rows_iff A).mpr ha.2.1] at ht
  exact_mod_cast ht.symm

end ASR312
