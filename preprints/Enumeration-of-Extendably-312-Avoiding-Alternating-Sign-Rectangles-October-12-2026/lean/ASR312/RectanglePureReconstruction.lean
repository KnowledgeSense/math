import ASR312.EmptyRowCounting

namespace ASR312

def rectanglePureTop {a r k : ℕ} (A : Rectangle ((a+1)+r) ((a+1)+k)) : Rectangle a a :=
  fun i j => A (i.castSucc.castAdd r) (j.succ.castAdd k)

def rectanglePureBottom {a r k : ℕ} (A : Rectangle ((a+1)+r) ((a+1)+k)) : Rectangle r k :=
  fun i j => A (i.natAdd (a+1)) (j.natAdd (a+1))

theorem rectangle_pure_reconstruction {a r k : ℕ} (A : Rectangle ((a+1)+r) ((a+1)+k))
    (ha : IsASR A) (he : ExtendablyAvoids312 A)
    (hp : A ((Fin.last a).castAdd r) 0 = .plus)
    (hpure : ∀ j, j ≠ 0 → A ((Fin.last a).castAdd r) j = .zero) :
    blockDiagonal (pivotInsert (rectanglePureTop A)) (rectanglePureBottom A) = A := by
  cases k with
  | zero =>
    let k : ℕ := 0
    funext i j
    have first (i : Fin ((a+1)+r)) (hi : i ≠ (Fin.last a).castAdd r) : A i 0 = .zero := by
      have hm := firstColumn_not_minus A ha i
      have hn : A i 0 ≠ .plus := fun h => hi (firstColumn_plus_unique A ha h hp)
      cases hx : A i 0 <;> simp_all
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_last_zero]
            change Entry.plus = A ((Fin.last a).castAdd r) 0
            exact hp.symm
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_last_succ]
            exact (hpure _ (by apply Fin.ne_of_val_ne; simp)).symm
        · simp only [blockDiagonal,Fin.append_left,Fin.append_right]
          exact (hpure _ (by apply Fin.ne_of_val_ne; simp)).symm
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_upper_zero]
            have hi : i.castSucc.castAdd r ≠ (Fin.last a).castAdd r := by
              apply Fin.ne_of_val_ne
              simp only [Fin.val_castAdd,Fin.val_castSucc,Fin.val_last]
              omega
            change Entry.zero = A (i.castSucc.castAdd r) 0
            exact (first _ hi).symm
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_upper]
            rfl
        · simp only [blockDiagonal,Fin.append_left,Fin.append_right]
          exact (rectangle_pivot_top_right_zero A he _ hp _ _
            (by change i.val < a; exact i.isLt) (by change a < a+1+j.val; omega)).symm
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [blockDiagonal,Fin.append_right,Fin.append_left]
        have hi : (Fin.last a).castAdd r < i.natAdd (a+1) := by
          change a < a+1+i.val; omega
        by_cases hj : j.val < a
        · exact (rectangle_pivot_below_left_zero A he _ hp _ _ hi hj).symm
        · have hjv : j.val = a := by omega
          have hej : j.castAdd k = (⟨a,by omega⟩ : Fin ((a+1)+k)) := Fin.ext hjv
          rw [hej]
          exact (rectangle_pure_below_pivot_zero A he _ hp (by change a < a+1+k; omega) hpure _ hi).symm
      · simp [blockDiagonal,rectanglePureBottom]
  | succ b =>
    let k := b+1
    funext i j
    have first (i : Fin ((a+1)+r)) (hi : i ≠ (Fin.last a).castAdd r) : A i 0 = .zero := by
      have hm := firstColumn_not_minus A ha i
      have hn : A i 0 ≠ .plus := fun h => hi (firstColumn_plus_unique A ha h hp)
      cases hx : A i 0 <;> simp_all
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_last_zero]
            change Entry.plus = A ((Fin.last a).castAdd r) 0
            exact hp.symm
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_last_succ]
            exact (hpure _ (by apply Fin.ne_of_val_ne; simp)).symm
        · simp only [blockDiagonal,Fin.append_left,Fin.append_right]
          exact (hpure _ (by apply Fin.ne_of_val_ne; simp)).symm
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_upper_zero]
            have hi : i.castSucc.castAdd r ≠ (Fin.last a).castAdd r := by
              apply Fin.ne_of_val_ne
              simp only [Fin.val_castAdd,Fin.val_castSucc,Fin.val_last]
              omega
            change Entry.zero = A (i.castSucc.castAdd r) 0
            exact (first _ hi).symm
          · simp only [blockDiagonal,Fin.append_left,pivotInsert_upper]
            rfl
        · simp only [blockDiagonal,Fin.append_left,Fin.append_right]
          exact (rectangle_pivot_top_right_zero A he _ hp _ _
            (by change i.val < a; exact i.isLt) (by change a < a+1+j.val; omega)).symm
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [blockDiagonal,Fin.append_right,Fin.append_left]
        have hi : (Fin.last a).castAdd r < i.natAdd (a+1) := by
          change a < a+1+i.val; omega
        by_cases hj : j.val < a
        · exact (rectangle_pivot_below_left_zero A he _ hp _ _ hi hj).symm
        · have hjv : j.val = a := by omega
          have hej : j.castAdd k = (⟨a,by omega⟩ : Fin ((a+1)+k)) := Fin.ext hjv
          rw [hej]
          exact (rectangle_pure_below_pivot_zero A he _ hp (by change a < a+1+k; omega) hpure _ hi).symm
      · simp [blockDiagonal,rectanglePureBottom]

theorem rectanglePureTop_valid {a r k : ℕ} (A : Rectangle ((a+1)+r) ((a+1)+k))
    (he : ExtendablyAvoids312 A) (hp : A ((Fin.last a).castAdd r) 0 = .plus) :
    IsASM (rectanglePureTop A) ∧ Avoids312 (rectanglePureTop A) := by
  cases k with
  | zero =>
    let k : ℕ := 0
    have hh := rectangleTopBlock_asm A he ((Fin.last a).castAdd r) hp
      (by change a < (a+1)+k; omega)
    exact hh
  | succ b =>
    let k := b+1
    have hh := rectangleTopBlock_asm A he ((Fin.last a).castAdd r) hp
      (by change a < (a+1)+k; omega)
    exact hh

theorem rectanglePureBottom_valid {a r k : ℕ} (A : Rectangle ((a+1)+r) ((a+1)+k))
    (ha : IsASR A) (he : ExtendablyAvoids312 A)
    (hp : A ((Fin.last a).castAdd r) 0 = .plus)
    (hpure : ∀ j, j ≠ 0 → A ((Fin.last a).castAdd r) j = .zero) :
    IsASR (rectanglePureBottom A) ∧ ExtendablyAvoids312 (rectanglePureBottom A) := by
  cases k with
  | zero =>
    let k : ℕ := 0
    have hr : ((a+1)+r)-(a+1) = r := by omega
    have hk : ((a+1)+k)-(a+1) = k := by omega
    have transport {r₁ k₁ r₂ k₂ : ℕ} (hr : r₁ = r₂) (hk : k₁ = k₂)
        (B : Rectangle r₁ k₁) (hb : IsASR B ∧ ExtendablyAvoids312 B) :
        IsASR (fun i j => B (Fin.cast hr.symm i) (Fin.cast hk.symm j)) ∧
        ExtendablyAvoids312 (fun i j => B (Fin.cast hr.symm i) (Fin.cast hk.symm j)) := by
      subst r₂; subst k₂; exact hb
    exact transport hr hk (suffixRectangle A (a+1))
      ⟨pureSuffix_asr A ha he _ hp (by change a < (a+1)+k; omega) hpure,
        pureSuffix_extendable A he _ hp (by change a < (a+1)+k; omega) hpure⟩
  | succ b =>
    let k := b+1
    have hr : ((a+1)+r)-(a+1) = r := by omega
    have hk : ((a+1)+k)-(a+1) = k := by omega
    have transport {r₁ k₁ r₂ k₂ : ℕ} (hr : r₁ = r₂) (hk : k₁ = k₂)
        (B : Rectangle r₁ k₁) (hb : IsASR B ∧ ExtendablyAvoids312 B) :
        IsASR (fun i j => B (Fin.cast hr.symm i) (Fin.cast hk.symm j)) ∧
        ExtendablyAvoids312 (fun i j => B (Fin.cast hr.symm i) (Fin.cast hk.symm j)) := by
      subst r₂; subst k₂; exact hb
    exact transport hr hk (suffixRectangle A (a+1))
      ⟨pureSuffix_asr A ha he _ hp (by change a < (a+1)+k; omega) hpure,
        pureSuffix_extendable A he _ hp (by change a < (a+1)+k; omega) hpure⟩

end ASR312
