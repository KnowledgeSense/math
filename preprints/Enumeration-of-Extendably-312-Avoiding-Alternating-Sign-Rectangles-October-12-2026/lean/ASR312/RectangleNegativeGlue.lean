import ASR312.ExtensionBoundary

namespace ASR312

def rectangleNegativeGlue {a r k : ℕ} (A : Rectangle (a+1) (a+1)) (B : Rectangle (r+1) (k+1)) :
    Rectangle ((a+1)+(r+1)) ((a+1)+(k+1)) :=
  Fin.append
    (fun i => Fin.append (Fin.cons .zero (fun j => A i j.castSucc))
      (Fin.cons (A i (Fin.last a)) (fun _ : Fin k => .zero)))
    (Fin.cons
      (Fin.append (Fin.cons .plus (fun _ : Fin a => .zero))
        (Fin.cons .minus (fun j => B 0 j.succ)))
      (fun i => Fin.append (fun _ : Fin (a+1) => .zero) (B i.succ)))

theorem rectangleNegativeGlue_row_top {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (i : Fin (a+1)) :
    nonzeroEntries (row (rectangleNegativeGlue A B) (i.castAdd (r+1))) =
      nonzeroEntries (row A i) := by
  conv_rhs => rw [row,List.ofFn_succ']
  simp only [row,rectangleNegativeGlue,Fin.append_left]
  rw [List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_succ,List.ofFn_const,List.concat_eq_append]
  cases A i (Fin.last a) <;> simp

theorem rectangleNegativeGlue_row_bottom {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (i : Fin r) :
    nonzeroEntries (row (rectangleNegativeGlue A B) (i.succ.natAdd (a+1))) =
      nonzeroEntries (row B i.succ) := by
  simp only [row,rectangleNegativeGlue,Fin.append_right,Fin.cons_succ]
  rw [List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_const]

theorem rectangleNegativeGlue_row_pivot {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (hb : IsASR B) (hn : ∃ j, B 0 j ≠ .zero)
    (hz : B 0 0 = .zero) :
    nonzeroEntries (row (rectangleNegativeGlue A B) ((0 : Fin (r+1)).natAdd (a+1))) =
      [.plus,.minus,.plus] := by
  have hh := asr_firstRow_tail_entries B hb hn hz
  simp only [nonzeroEntries] at hh
  simp only [row,rectangleNegativeGlue,Fin.append_right,Fin.cons_zero]
  rw [List.ofFn_fin_append]
  simp only [nonzeroEntries,List.filter_append]
  simp [List.ofFn_succ,List.ofFn_const,hh]

theorem rectangleNegativeGlue_extendable {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (ha : IsASM A) (hav : Avoids312 A)
    (he : ExtendablyAvoids312 B) (hz : B 0 0 = .zero) :
    ExtendablyAvoids312 (rectangleNegativeGlue A B) := by
  obtain ⟨n,hr,hk,C,hC,hCv,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    have hzC : C 0 0 = .zero := by
      have hh := hmatch 0 0
      have hi : Fin.castLE hr 0 = (0 : Fin (n+1)) := Fin.ext rfl
      have hj : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [hi,hj,hz] using hh
    refine ⟨(a+1)+(n+1),by omega,by omega,negativeGlue A C,
      negativeGlue_asm A C ha hC hzC,negativeGlue_avoids312 A C hav hCv,?_⟩
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have ei : Fin.castLE (by omega : (a+1)+(r+1) ≤ (a+1)+(n+1)) (i.castAdd (r+1)) =
          i.castAdd (n+1) := Fin.ext rfl
      rw [ei]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · have ej : Fin.castLE (by omega : (a+1)+(k+1) ≤ (a+1)+(n+1)) (j.castAdd (k+1)) =
            j.castAdd (n+1) := Fin.ext rfl
        rw [ej]
        simp [negativeGlue,rectangleNegativeGlue]
      · have ej : Fin.castLE (by omega : (a+1)+(k+1) ≤ (a+1)+(n+1)) (j.natAdd (a+1)) =
            (Fin.castLE hk j).natAdd (a+1) := Fin.ext rfl
        rw [ej]
        refine Fin.cases ?_ (fun j => ?_) j
        · have ej0 : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
          simp [negativeGlue,rectangleNegativeGlue,ej0]
        · have ejS : Fin.castLE hk j.succ = (Fin.castLE (by omega : k ≤ n) j).succ := Fin.ext rfl
          simp [negativeGlue,rectangleNegativeGlue,ejS]
    · have ei : Fin.castLE (by omega : (a+1)+(r+1) ≤ (a+1)+(n+1)) (i.natAdd (a+1)) =
          (Fin.castLE hr i).natAdd (a+1) := Fin.ext rfl
      rw [ei]
      refine Fin.cases ?_ (fun i => ?_) i
      · have ei0 : Fin.castLE hr 0 = (0 : Fin (n+1)) := Fin.ext rfl
        rw [ei0]
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · have ej : Fin.castLE (by omega : (a+1)+(k+1) ≤ (a+1)+(n+1)) (j.castAdd (k+1)) =
              j.castAdd (n+1) := Fin.ext rfl
          rw [ej]
          simp [negativeGlue,rectangleNegativeGlue]
        · have ej : Fin.castLE (by omega : (a+1)+(k+1) ≤ (a+1)+(n+1)) (j.natAdd (a+1)) =
              (Fin.castLE hk j).natAdd (a+1) := Fin.ext rfl
          rw [ej]
          refine Fin.cases ?_ (fun j => ?_) j
          · have ej0 : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
            simp [negativeGlue,rectangleNegativeGlue,ej0]
          · have ejS : Fin.castLE hk j.succ = (Fin.castLE (by omega : k ≤ n) j).succ := Fin.ext rfl
            simp only [negativeGlue,rectangleNegativeGlue,Fin.append_right,Fin.cons_zero,ejS,Fin.cons_succ]
            simpa only [ei0,ejS] using hmatch 0 j.succ
      · have eiS : Fin.castLE hr i.succ = (Fin.castLE (by omega : r ≤ n) i).succ := Fin.ext rfl
        rw [eiS]
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · have ej : Fin.castLE (by omega : (a+1)+(k+1) ≤ (a+1)+(n+1)) (j.castAdd (k+1)) =
              j.castAdd (n+1) := Fin.ext rfl
          rw [ej]
          simp [negativeGlue,rectangleNegativeGlue]
        · have ej : Fin.castLE (by omega : (a+1)+(k+1) ≤ (a+1)+(n+1)) (j.natAdd (a+1)) =
              (Fin.castLE hk j).natAdd (a+1) := Fin.ext rfl
          rw [ej]
          simp only [negativeGlue,rectangleNegativeGlue,Fin.append_right,Fin.cons_succ]
          simpa only [eiS] using hmatch i.succ j

theorem rectangleNegativeGlue_asr {a r k : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (r+1) (k+1)) (ha : IsASM A) (hav : Avoids312 A)
    (hb : IsASR B) (he : ExtendablyAvoids312 B) (hn : ∃ j, B 0 j ≠ .zero)
    (hz : B 0 0 = .zero) : IsASR (rectangleNegativeGlue A B) := by
  apply extendable_asr_of_ends _ (rectangleNegativeGlue_extendable A B ha hav he hz)
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [EndsPositive,rectangleNegativeGlue_row_top] using (ha.1.1 i).2.2
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [EndsPositive,rectangleNegativeGlue_row_pivot A B hb hn hz]
    · simpa only [EndsPositive,rectangleNegativeGlue_row_bottom] using (hb.1 i.succ).2.2

end ASR312
