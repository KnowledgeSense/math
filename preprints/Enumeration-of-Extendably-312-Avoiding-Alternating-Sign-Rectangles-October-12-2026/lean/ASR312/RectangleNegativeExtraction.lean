import ASR312.RectangleNegativeGlue

namespace ASR312

def rectangleNegativeTop {a r k : ℕ} (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) :
    Rectangle (a+1) (a+1) := fun i j => A (i.castAdd (r+1)) ⟨j.val+1,by omega⟩

def rectangleNegativeBottom {a r k : ℕ} (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) :
    Rectangle (r+1) (k+1) := fun i j =>
      if i = 0 ∧ j = 0 then .zero else A (i.natAdd (a+1)) (j.natAdd (a+1))

theorem rectangleNegativeTop_valid {a r k : ℕ} (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1)))
    (he : ExtendablyAvoids312 A) (hp : A ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus) :
    IsASM (rectangleNegativeTop A) ∧ Avoids312 (rectangleNegativeTop A) := by
  exact rectangleTopBlock_asm A he ((0 : Fin (r+1)).natAdd (a+1)) hp (by simp)

theorem rectangleNegativeBottom_extendable {a r k : ℕ}
    (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) (he : ExtendablyAvoids312 A)
    (hp : A ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus)
    (hm : A ((0 : Fin (r+1)).natAdd (a+1)) ((0 : Fin (k+1)).natAdd (a+1)) = .minus) :
    ExtendablyAvoids312 (rectangleNegativeBottom A) := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    let p : Fin (n+1) := ⟨a+1,by omega⟩
    have hip : Fin.castLE hr ((0 : Fin (r+1)).natAdd (a+1)) = p := Fin.ext (by simp [p])
    have hjp : Fin.castLE hk ((0 : Fin (k+1)).natAdd (a+1)) = p := Fin.ext (by simp [p])
    have hj0 : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
    have hBp : B p 0 = .plus := by simpa only [hip,hj0,hp] using hmatch ((0 : Fin (r+1)).natAdd (a+1)) 0
    have hBm : B p p = .minus := by
      simpa only [hip,hjp,hm] using hmatch ((0 : Fin (r+1)).natAdd (a+1)) ((0 : Fin (k+1)).natAdd (a+1))
    refine ⟨n+1-p.val,by dsimp [p]; omega,by dsimp [p]; omega,repairedLowerBlock B p,
      repairedLowerBlock_asm B hB hav p hBp hBm,repairedLowerBlock_avoids312 B hav p,?_⟩
    intro i j
    simp only [repairedLowerBlock,rectangleNegativeBottom,Fin.val_castLE,Fin.ext_iff,Fin.val_zero]
    by_cases hz : i.val = 0 ∧ j.val = 0
    · simp [hz]
    · simp only [hz,ite_false]
      exact hmatch (i.natAdd (a+1)) (j.natAdd (a+1))

theorem rectangleNegativeBottom_nonemptyFirstRow {a r k : ℕ}
    (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) (ha : IsASR A) (he : ExtendablyAvoids312 A)
    (hp : A ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus)
    (hm : A ((0 : Fin (r+1)).natAdd (a+1)) ((0 : Fin (k+1)).natAdd (a+1)) = .minus) :
    ∃ j, rectangleNegativeBottom A 0 j ≠ .zero := by
  rcases row_firstColumn_structure A ha he _ hp with hh | ⟨z,u,hz0,hzu,hz,hu,_⟩
  · have hn : (0 : Fin (k+1)).natAdd (a+1) ≠ 0 := by apply Fin.ne_of_val_ne; simp
    rw [hh _ hn] at hm
    cases hm
  · have hpz := rectangle_negative_pivot_diagonal A he _ z hp hz
    have huz : a+1 < u.val := by change z.val < u.val at hzu; simp only [Fin.val_natAdd,Fin.val_zero,Nat.add_zero] at hpz; omega
    have hub := u.isLt
    change u.val < (a+1)+(k+1) at hub
    let j : Fin (k+1) := ⟨u.val-(a+1),by omega⟩
    have hj0 : j ≠ 0 := by apply Fin.ne_of_val_ne; dsimp [j]; omega
    have hju : j.natAdd (a+1) = u := Fin.ext (by dsimp [j]; omega)
    refine ⟨j,?_⟩
    simp only [rectangleNegativeBottom,hj0,and_false,ite_false,hju,hu]
    decide

theorem rectangleNegativeBottom_row_entries {a r k : ℕ}
    (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) (he : ExtendablyAvoids312 A)
    (hp : A ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus) (i : Fin r) :
    nonzeroEntries (row (rectangleNegativeBottom A) i.succ) =
      nonzeroEntries (row A (i.succ.natAdd (a+1))) := by
  have hf : row (rectangleNegativeBottom A) i.succ =
      (row A (i.succ.natAdd (a+1))).drop (a+1) := by
    simp only [row,drop_ofFn,Nat.add_sub_cancel_left]
    congr 1
  rw [hf]
  apply nonzeroEntries_drop_ofFn
  intro j hj
  exact rectangle_pivot_below_left_zero A he _ hp _ j
    (by change a+1 < a+1+(i.val+1); omega) hj

theorem rectangleNegativeBottom_asr {a r k : ℕ}
    (A : Rectangle ((a+1)+(r+1)) ((a+1)+(k+1))) (ha : IsASR A) (he : ExtendablyAvoids312 A)
    (hp : A ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus)
    (hm : A ((0 : Fin (r+1)).natAdd (a+1)) ((0 : Fin (k+1)).natAdd (a+1)) = .minus) :
    IsASR (rectangleNegativeBottom A) := by
  have heB := rectangleNegativeBottom_extendable A he hp hm
  apply extendable_asr_of_ends _ heB
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [EndsPositive,extendable_firstRow_entries _ heB
      (rectangleNegativeBottom_nonemptyFirstRow A ha he hp hm)]
  · simpa only [EndsPositive,rectangleNegativeBottom_row_entries A he hp] using
      (ha.1 (i.succ.natAdd (a+1))).2.2

end ASR312
