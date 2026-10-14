import ASR312.RepairedASM

namespace ASR312

 def directSum {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) : Rectangle (a+b) (a+b) :=
  Fin.append (fun i => Fin.append (A i) (fun _ => .zero))
    (fun i => Fin.append (fun _ => .zero) (B i))

 theorem directSum_left_left {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (i j : Fin a) :
    directSum A B (i.castAdd b) (j.castAdd b) = A i j := by simp [directSum]

 theorem directSum_left_right {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (i : Fin a) (j : Fin b) :
    directSum A B (i.castAdd b) (j.natAdd a) = .zero := by simp [directSum]

 theorem directSum_right_left {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (i : Fin b) (j : Fin a) :
    directSum A B (i.natAdd a) (j.castAdd b) = .zero := by simp [directSum]

 theorem directSum_right_right {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (i j : Fin b) :
    directSum A B (i.natAdd a) (j.natAdd a) = B i j := by simp [directSum]

 theorem directSum_row_left {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (i : Fin a) :
    nonzeroEntries (row (directSum A B) (i.castAdd b)) = nonzeroEntries (row A i) := by
  simp [row,directSum,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem directSum_row_right {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (i : Fin b) :
    nonzeroEntries (row (directSum A B) (i.natAdd a)) = nonzeroEntries (row B i) := by
  simp [row,directSum,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem directSum_col_left {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (j : Fin a) :
    nonzeroEntries (col (directSum A B) (j.castAdd b)) = nonzeroEntries (col A j) := by
  have hf : (fun i => directSum A B i (j.castAdd b)) =
      Fin.append (fun i => A i j) (fun _ : Fin b => Entry.zero) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [directSum]
  simp [col,hf,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem directSum_col_right {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b) (j : Fin b) :
    nonzeroEntries (col (directSum A B) (j.natAdd a)) = nonzeroEntries (col B j) := by
  have hf : (fun i => directSum A B i (j.natAdd a)) =
      Fin.append (fun _ : Fin a => Entry.zero) (fun i => B i j) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [directSum]
  simp [col,hf,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem directSum_asm {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b)
    (ha : IsASM A) (hb : IsASM B) : IsASM (directSum A B) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Alternates,StartsPositive,EndsPositive,directSum_row_left] using ha.1.1 i
    · simpa only [Alternates,StartsPositive,EndsPositive,directSum_row_right] using hb.1.1 i
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Alternates,StartsPositive,directSum_col_left] using ha.1.2 j
    · simpa only [Alternates,StartsPositive,directSum_col_right] using hb.1.2 j
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · obtain ⟨j,hj⟩ := ha.2.1 i
      exact ⟨j.castAdd b,by simpa only [directSum_left_left] using hj⟩
    · obtain ⟨j,hj⟩ := hb.2.1 i
      exact ⟨j.natAdd a,by simpa only [directSum_right_right] using hj⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · obtain ⟨⟨i,hi⟩,hend⟩ := ha.2.2 j
      exact ⟨⟨i.castAdd b,by simpa only [directSum_left_left] using hi⟩,
        by simpa only [EndsPositive,directSum_col_left] using hend⟩
    · obtain ⟨⟨i,hi⟩,hend⟩ := hb.2.2 j
      exact ⟨⟨i.natAdd a,by simpa only [directSum_right_right] using hi⟩,
        by simpa only [EndsPositive,directSum_col_right] using hend⟩

 theorem directSum_plus_same_side {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b)
    (i j : Fin (a+b)) (h : directSum A B i j = .plus) : i.val < a ↔ j.val < a := by
  revert h
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro _
      simp only [Fin.val_castAdd]
      exact iff_of_true i.isLt j.isLt
    · simp [directSum]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [directSum]
    · intro _
      simp only [Fin.val_natAdd]
      omega

 theorem directSum_of_left {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b)
    (i j : Fin (a+b)) (hi : i.val < a) (hj : j.val < a) :
    directSum A B i j = A ⟨i.val,hi⟩ ⟨j.val,hj⟩ := by
  have ei : (⟨i.val,hi⟩ : Fin a).castAdd b = i := Fin.ext rfl
  have ej : (⟨j.val,hj⟩ : Fin a).castAdd b = j := Fin.ext rfl
  simpa only [ei,ej] using directSum_left_left A B ⟨i.val,hi⟩ ⟨j.val,hj⟩

 theorem directSum_of_right {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b)
    (i j : Fin (a+b)) (hi : a ≤ i.val) (hj : a ≤ j.val) :
    directSum A B i j = B ⟨i.val-a,by omega⟩ ⟨j.val-a,by omega⟩ := by
  have ei : (⟨i.val-a,by omega⟩ : Fin b).natAdd a = i := by apply Fin.ext; simp; omega
  have ej : (⟨j.val-a,by omega⟩ : Fin b).natAdd a = j := by apply Fin.ext; simp; omega
  simpa only [ei,ej] using directSum_right_right A B ⟨i.val-a,by omega⟩ ⟨j.val-a,by omega⟩

 theorem directSum_avoids312 {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b)
    (ha : Avoids312 A) (hb : Avoids312 B) : Avoids312 (directSum A B) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  have hs13 := directSum_plus_same_side A B i₁ j₃ h13
  have hs21 := directSum_plus_same_side A B i₂ j₁ h21
  have hs32 := directSum_plus_same_side A B i₃ j₂ h32
  change i₁.val < i₂.val at h12
  change i₂.val < i₃.val at h23
  change j₁.val < j₂.val at hj12
  change j₂.val < j₃.val at hj23
  by_cases hia : i₁.val < a
  · have hj3a := hs13.mp hia
    have hj2a : j₂.val < a := by omega
    have hi3a := hs32.mpr hj2a
    have hi2a : i₂.val < a := by omega
    have hj1a : j₁.val < a := by omega
    rw [directSum_of_left A B i₁ j₃ hia hj3a] at h13
    rw [directSum_of_left A B i₂ j₁ hi2a hj1a] at h21
    rw [directSum_of_left A B i₃ j₂ hi3a hj2a] at h32
    exact ha ⟨⟨i₁.val,hia⟩,⟨i₂.val,hi2a⟩,⟨i₃.val,hi3a⟩,
      ⟨j₁.val,hj1a⟩,⟨j₂.val,hj2a⟩,⟨j₃.val,hj3a⟩,h12,h23,hj12,hj23,h13,h21,h32⟩
  · have hi1 : a ≤ i₁.val := by omega
    have hi2 : a ≤ i₂.val := by omega
    have hi3 : a ≤ i₃.val := by omega
    have hj1 : a ≤ j₁.val := by have := hs21.not.mp (by omega); omega
    have hj2 : a ≤ j₂.val := by have := hs32.not.mp (by omega); omega
    have hj3 : a ≤ j₃.val := by have := hs13.not.mp hia; omega
    rw [directSum_of_right A B i₁ j₃ hi1 hj3] at h13
    rw [directSum_of_right A B i₂ j₁ hi2 hj1] at h21
    rw [directSum_of_right A B i₃ j₂ hi3 hj2] at h32
    refine hb ⟨⟨i₁.val-a,by omega⟩,⟨i₂.val-a,by omega⟩,⟨i₃.val-a,by omega⟩,
      ⟨j₁.val-a,by omega⟩,⟨j₂.val-a,by omega⟩,⟨j₃.val-a,by omega⟩,?_,?_,?_,?_,h13,h21,h32⟩
    · change i₁.val-a < i₂.val-a; omega
    · change i₂.val-a < i₃.val-a; omega
    · change j₁.val-a < j₂.val-a; omega
    · change j₂.val-a < j₃.val-a; omega

end ASR312
