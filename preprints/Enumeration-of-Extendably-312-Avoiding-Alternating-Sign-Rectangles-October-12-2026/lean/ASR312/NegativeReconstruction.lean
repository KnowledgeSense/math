import ASR312.NegativeGlueAvoidance
import ASR312.PureReconstruction

namespace ASR312

 theorem negative_pivot_left_zero {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hm : A p p = .minus) (j : Fin (n+1)) (hj0 : j ≠ 0) (hjp : j < p) : A p j = .zero := by
  have hp0 : p ≠ 0 := by intro he; subst p; rw [hp] at hm; cases hm
  rcases row_firstColumn_structure A ha.1 ((asm_extendable_iff A ha).mpr hav) p hp with hh | ⟨z,u,hz0,hzu,hz,hu,hh⟩
  · rw [hh p hp0] at hm; cases hm
  · have he : z = p := asm_row_minus_unique A ha hav p hz hm
    subst z
    exact hh j hj0 (ne_of_lt hjp) (ne_of_lt (lt_trans hjp hzu))

 def negativeTopBlock {a b : ℕ} (A : Rectangle ((a+1)+(b+1)) ((a+1)+(b+1))) :
    Rectangle (a+1) (a+1) :=
  fun i j => A (i.castAdd (b+1)) ⟨j.val+1,by omega⟩

 def negativeLowerBlock {a b : ℕ} (A : Rectangle ((a+1)+(b+1)) ((a+1)+(b+1))) :
    Rectangle (b+1) (b+1) :=
  fun i j => if i = 0 ∧ j = 0 then .zero else A (i.natAdd (a+1)) (j.natAdd (a+1))

 theorem negative_reconstruction {a b : ℕ} (A : Rectangle ((a+1)+(b+1)) ((a+1)+(b+1)))
    (ha : IsASM A) (hav : Avoids312 A)
    (hp : A ((0 : Fin (b+1)).natAdd (a+1)) 0 = .plus)
    (hm : A ((0 : Fin (b+1)).natAdd (a+1)) ((0 : Fin (b+1)).natAdd (a+1)) = .minus) :
    negativeGlue (negativeTopBlock A) (negativeLowerBlock A) = A := by
  funext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [negativeGlue,Fin.append_left,Fin.cons_zero]
        exact (firstColumn_above_zero A ha.1 _ hp _ (by change i.val < a+1; omega)).symm
      · simp only [negativeGlue,negativeTopBlock,Fin.append_left,Fin.cons_succ]
        congr 1
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [negativeGlue,negativeTopBlock,Fin.append_left,Fin.append_right,Fin.cons_zero]
        congr 1
      · simp only [negativeGlue,Fin.append_left,Fin.append_right,Fin.cons_succ]
        exact ((asm_pivot_top_facts A ha hav _ hp).1 _ _
          (by change i.val < a+1; omega) (by change a+1 < a+1+(j.val+1); omega)).symm
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [negativeGlue,Fin.append_right,Fin.cons_zero,Fin.append_left]
          change Entry.plus = A ((0 : Fin (b+1)).natAdd (a+1)) 0
          exact hp.symm
        · simp only [negativeGlue,Fin.append_right,Fin.cons_zero,Fin.append_left,Fin.cons_succ]
          exact (negative_pivot_left_zero A ha hav _ hp hm _
            (by apply Fin.ne_of_val_ne; simp) (by change j.val+1 < a+1; omega)).symm
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa [negativeGlue] using hm.symm
        · simp [negativeGlue,negativeLowerBlock]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [negativeGlue,Fin.append_right,Fin.cons_succ,Fin.append_left]
        exact (asm_below_left_zero A ha hav _ hp _ _
          (by change a+1 < a+1+(i.val+1); omega) (by change j.val < a+1; omega)).symm
      · simp [negativeGlue,negativeLowerBlock]

 theorem negativeTopBlock_asm {a b : ℕ} (A : Rectangle ((a+1)+(b+1)) ((a+1)+(b+1)))
    (ha : IsASM A) (hav : Avoids312 A)
    (hp : A ((0 : Fin (b+1)).natAdd (a+1)) 0 = .plus) :
    IsASM (negativeTopBlock A) ∧ Avoids312 (negativeTopBlock A) := by
  exact asm_pivot_topBlock A ha hav _ hp

 theorem negativeLowerBlock_corner {a b : ℕ} (A : Rectangle ((a+1)+(b+1)) ((a+1)+(b+1))) :
    negativeLowerBlock A 0 0 = .zero := by simp [negativeLowerBlock]

 theorem negativeLowerBlock_asm {a b : ℕ} (A : Rectangle ((a+1)+(b+1)) ((a+1)+(b+1)))
    (ha : IsASM A) (hav : Avoids312 A)
    (hp : A ((0 : Fin (b+1)).natAdd (a+1)) 0 = .plus)
    (hm : A ((0 : Fin (b+1)).natAdd (a+1)) ((0 : Fin (b+1)).natAdd (a+1)) = .minus) :
    IsASM (negativeLowerBlock A) ∧ Avoids312 (negativeLowerBlock A) := by
  have transport {u v : ℕ} (h : u = v) (D : Rectangle v v)
      (hd : IsASM D ∧ Avoids312 D) :
      IsASM (fun i j => D (Fin.cast h i) (Fin.cast h j)) ∧
      Avoids312 (fun i j => D (Fin.cast h i) (Fin.cast h j)) := by subst v; exact hd
  have hh := transport (by omega : b+1 = (a+1)+(b+1)-(a+1))
    (repairedLowerBlock A ((0 : Fin (b+1)).natAdd (a+1)))
    ⟨repairedLowerBlock_asm A ha hav _ hp hm,repairedLowerBlock_avoids312 A hav _⟩
  have he : (fun i j : Fin (b+1) => repairedLowerBlock A ((0 : Fin (b+1)).natAdd (a+1))
      (Fin.cast (by simp) i) (Fin.cast (by simp) j)) = negativeLowerBlock A := by
    funext i j
    simp only [repairedLowerBlock,negativeLowerBlock,Fin.val_natAdd,Fin.val_zero,Nat.add_zero,Fin.ext_iff]
    rfl
  exact he ▸ hh

 theorem negativeGlue_topBlock {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) : negativeTopBlock (negativeGlue A B) = A := by
  funext i j
  exact negativeGlue_top_value A B i j

 theorem negativeGlue_lowerBlock {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (hz : B 0 0 = .zero) :
    negativeLowerBlock (negativeGlue A B) = B := by
  funext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [negativeLowerBlock,negativeGlue,hz]
  · simp [negativeLowerBlock,negativeGlue]

end ASR312
