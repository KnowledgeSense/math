import ASR312.DirectSum

namespace ASR312

 def pivotInsert {n : ℕ} (A : Rectangle n n) : Rectangle (n+1) (n+1) :=
  Fin.snoc (fun i => Fin.cons .zero (A i)) (Fin.cons .plus (fun _ => .zero))

 theorem pivotInsert_upper {n : ℕ} (A : Rectangle n n) (i j : Fin n) :
    pivotInsert A i.castSucc j.succ = A i j := by simp [pivotInsert]

 theorem pivotInsert_upper_zero {n : ℕ} (A : Rectangle n n) (i : Fin n) :
    pivotInsert A i.castSucc 0 = .zero := by simp [pivotInsert]

 theorem pivotInsert_last_zero {n : ℕ} (A : Rectangle n n) :
    pivotInsert A (Fin.last n) 0 = .plus := by simp [pivotInsert]

 theorem pivotInsert_last_succ {n : ℕ} (A : Rectangle n n) (j : Fin n) :
    pivotInsert A (Fin.last n) j.succ = .zero := by simp [pivotInsert]

 theorem pivotInsert_row_upper {n : ℕ} (A : Rectangle n n) (i : Fin n) :
    nonzeroEntries (row (pivotInsert A) i.castSucc) = nonzeroEntries (row A i) := by
  simp [row,pivotInsert,List.ofFn_succ,nonzeroEntries]

 theorem pivotInsert_row_last {n : ℕ} (A : Rectangle n n) :
    nonzeroEntries (row (pivotInsert A) (Fin.last n)) = [.plus] := by
  simp [row,pivotInsert,List.ofFn_succ,nonzeroEntries,List.ofFn_const]

 theorem pivotInsert_col_zero {n : ℕ} (A : Rectangle n n) :
    nonzeroEntries (col (pivotInsert A) 0) = [.plus] := by
  have he : (fun i => pivotInsert A i 0) =
      (fun i => if i = Fin.last n then Entry.plus else .zero) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [pivotInsert]
  rw [col,he]
  exact nonzero_ofFn_single (Fin.last n)

 theorem pivotInsert_col_succ {n : ℕ} (A : Rectangle n n) (j : Fin n) :
    nonzeroEntries (col (pivotInsert A) j.succ) = nonzeroEntries (col A j) := by
  unfold col
  rw [List.ofFn_succ']
  simp [pivotInsert,nonzeroEntries,List.concat_eq_append]

 theorem pivotInsert_asm {n : ℕ} (A : Rectangle n n) (ha : IsASM A) : IsASM (pivotInsert A) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [Alternates,StartsPositive,EndsPositive,pivotInsert_row_last]
    · simpa only [Alternates,StartsPositive,EndsPositive,pivotInsert_row_upper] using ha.1.1 i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Alternates,StartsPositive,pivotInsert_col_zero]
    · simpa only [Alternates,StartsPositive,pivotInsert_col_succ] using ha.1.2 j
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact ⟨0,by simp [pivotInsert]⟩
    · obtain ⟨j,hj⟩ := ha.2.1 i
      exact ⟨j.succ,by simpa only [pivotInsert_upper] using hj⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ⟨⟨Fin.last n,by simp [pivotInsert]⟩,by simp [EndsPositive,pivotInsert_col_zero]⟩
    · obtain ⟨⟨i,hi⟩,hend⟩ := ha.2.2 j
      exact ⟨⟨i.castSucc,by simpa only [pivotInsert_upper] using hi⟩,
        by simpa only [EndsPositive,pivotInsert_col_succ] using hend⟩

 theorem pivotInsert_last_plus {n : ℕ} (A : Rectangle n n) (j : Fin (n+1))
    (h : pivotInsert A (Fin.last n) j = .plus) : j = 0 := by
  revert h
  refine Fin.cases (fun _ => rfl) (fun j => ?_) j
  simp [pivotInsert]

 theorem pivotInsert_upper_plus_not_zero {n : ℕ} (A : Rectangle n n) (i j : Fin (n+1))
    (hi : i.val < n) (h : pivotInsert A i j = .plus) : j ≠ 0 := by
  intro hj
  subst j
  have he : (⟨i.val,hi⟩ : Fin n).castSucc = i := Fin.ext rfl
  have hh := pivotInsert_upper_zero A ⟨i.val,hi⟩
  rw [he,h] at hh
  cases hh

 theorem pivotInsert_of_upper {n : ℕ} (A : Rectangle n n) (i j : Fin (n+1))
    (hi : i.val < n) (hj : j ≠ 0) :
    pivotInsert A i j = A ⟨i.val,hi⟩ (j.pred hj) := by
  have ei : (⟨i.val,hi⟩ : Fin n).castSucc = i := Fin.ext rfl
  have ej : (j.pred hj).succ = j := Fin.succ_pred j hj
  simpa only [ei,ej] using pivotInsert_upper A ⟨i.val,hi⟩ (j.pred hj)

 theorem pivotInsert_avoids312 {n : ℕ} (A : Rectangle n n) (ha : Avoids312 A) :
    Avoids312 (pivotInsert A) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  have hi3 : i₃.val < n := by
    by_contra hn
    have he : i₃ = Fin.last n := Fin.eq_last_of_not_lt hn
    rw [he] at h32
    have hj2 := pivotInsert_last_plus A j₂ h32
    rw [hj2] at hj12
    exact not_lt_of_ge (Fin.zero_le j₁) hj12
  have hi2 : i₂.val < n := lt_trans h23 hi3
  have hi1 : i₁.val < n := lt_trans h12 hi2
  have hj1 := pivotInsert_upper_plus_not_zero A i₂ j₁ hi2 h21
  have hj2 := pivotInsert_upper_plus_not_zero A i₃ j₂ hi3 h32
  have hj3 := pivotInsert_upper_plus_not_zero A i₁ j₃ hi1 h13
  rw [pivotInsert_of_upper A i₁ j₃ hi1 hj3] at h13
  rw [pivotInsert_of_upper A i₂ j₁ hi2 hj1] at h21
  rw [pivotInsert_of_upper A i₃ j₂ hi3 hj2] at h32
  refine ha ⟨⟨i₁.val,hi1⟩,⟨i₂.val,hi2⟩,⟨i₃.val,hi3⟩,
    j₁.pred hj1,j₂.pred hj2,j₃.pred hj3,h12,h23,?_,?_,h13,h21,h32⟩
  · exact Fin.pred_lt_pred_iff.mpr hj12
  · exact Fin.pred_lt_pred_iff.mpr hj23

end ASR312
