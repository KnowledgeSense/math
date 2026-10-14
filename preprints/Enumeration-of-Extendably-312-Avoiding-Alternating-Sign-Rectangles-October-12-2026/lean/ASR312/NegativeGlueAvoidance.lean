import ASR312.NegativeGlueASM

namespace ASR312

 theorem negativeGlue_top_plus {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (i : Fin (a+1)) (j : Fin ((a+1)+(b+1)))
    (h : negativeGlue A B (i.castAdd (b+1)) j = .plus) : 0 < j.val ∧ j.val ≤ a+1 := by
  revert h
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [negativeGlue]
    · intro _; simp only [Fin.val_castAdd,Fin.val_succ]; omega
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _; simp only [Fin.val_natAdd,Fin.val_zero]; omega
    · simp [negativeGlue]

 theorem negativeGlue_bottom_plus {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (i : Fin (b+1)) (j : Fin ((a+1)+(b+1)))
    (h : negativeGlue A B (i.natAdd (a+1)) j = .plus) :
    (i.val = 0 ∧ j.val = 0) ∨ a+1 ≤ j.val := by
  revert h
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _; exact Or.inl ⟨rfl,rfl⟩
      · simp [negativeGlue]
    · intro _; right; simp only [Fin.val_natAdd]; omega
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [negativeGlue]
    · intro _; right; simp only [Fin.val_natAdd]; omega

 theorem negativeGlue_top_value {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (i : Fin (a+1)) (j : Fin (a+1)) :
    negativeGlue A B (i.castAdd (b+1)) ⟨j.val+1,by omega⟩ = A i j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have he : (⟨(Fin.last a).val+1,by omega⟩ : Fin ((a+1)+(b+1))) =
        (0 : Fin (b+1)).natAdd (a+1) := by apply Fin.ext; simp
    rw [he]; simp [negativeGlue]
  · have he : (⟨j.castSucc.val+1,by omega⟩ : Fin ((a+1)+(b+1))) =
        j.succ.castAdd (b+1) := by apply Fin.ext; rfl
    rw [he]; simp [negativeGlue]

 theorem negativeGlue_bottom_value {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (i j : Fin (b+1))
    (h : negativeGlue A B (i.natAdd (a+1)) (j.natAdd (a+1)) = .plus) : B i j = .plus := by
  revert h
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [negativeGlue]
  · simp [negativeGlue]

 theorem negativeGlue_top_plus_value {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (i j : Fin ((a+1)+(b+1))) (hi : i.val < a+1)
    (h : negativeGlue A B i j = .plus) :
    ∃ (hj0 : 0 < j.val) (hj : j.val ≤ a+1),
      A ⟨i.val,hi⟩ ⟨j.val-1,by omega⟩ = .plus := by
  have ei : (⟨i.val,hi⟩ : Fin (a+1)).castAdd (b+1) = i := Fin.ext rfl
  have hh := negativeGlue_top_plus A B ⟨i.val,hi⟩ j (by simpa only [ei] using h)
  refine ⟨hh.1,hh.2,?_⟩
  have ej : (⟨(j.val-1)+1,by omega⟩ : Fin ((a+1)+(b+1))) = j := by apply Fin.ext; change j.val-1+1 = j.val; omega
  have he := negativeGlue_top_value A B ⟨i.val,hi⟩ ⟨j.val-1,by omega⟩
  simpa only [ei,ej,h] using he.symm

 theorem negativeGlue_bottom_plus_value {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (i j : Fin ((a+1)+(b+1))) (hi : a+1 ≤ i.val)
    (h : negativeGlue A B i j = .plus) :
    (i.val = a+1 ∧ j.val = 0) ∨
      ∃ hj : a+1 ≤ j.val, B ⟨i.val-(a+1),by omega⟩ ⟨j.val-(a+1),by omega⟩ = .plus := by
  have ei : (⟨i.val-(a+1),by omega⟩ : Fin (b+1)).natAdd (a+1) = i := by
    apply Fin.ext; simp; omega
  have hh := negativeGlue_bottom_plus A B ⟨i.val-(a+1),by omega⟩ j (by simpa only [ei] using h)
  rcases hh with hh | hj
  · left; change i.val-(a+1) = 0 ∧ j.val = 0 at hh
    constructor <;> omega
  · right; refine ⟨hj,?_⟩
    have ej : (⟨j.val-(a+1),by omega⟩ : Fin (b+1)).natAdd (a+1) = j := by
      apply Fin.ext; simp; omega
    apply negativeGlue_bottom_value A B
    simpa only [ei,ej] using h

 theorem negativeGlue_avoids312 {a b : ℕ} (A : Rectangle (a+1) (a+1))
    (B : Rectangle (b+1) (b+1)) (ha : Avoids312 A) (hb : Avoids312 B) :
    Avoids312 (negativeGlue A B) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  change i₁.val < i₂.val at h12
  change i₂.val < i₃.val at h23
  change j₁.val < j₂.val at hj12
  change j₂.val < j₃.val at hj23
  by_cases hi1 : i₁.val < a+1
  · obtain ⟨hj30,hj3,hA13⟩ := negativeGlue_top_plus_value A B i₁ j₃ hi1 h13
    have hi3 : i₃.val < a+1 := by
      by_contra hn
      rcases negativeGlue_bottom_plus_value A B i₃ j₂ (by omega) h32 with hh | ⟨hh,_⟩ <;> omega
    have hi2 : i₂.val < a+1 := by omega
    obtain ⟨hj10,hj1,hA21⟩ := negativeGlue_top_plus_value A B i₂ j₁ hi2 h21
    obtain ⟨hj20,hj2,hA32⟩ := negativeGlue_top_plus_value A B i₃ j₂ hi3 h32
    refine ha ⟨⟨i₁.val,hi1⟩,⟨i₂.val,hi2⟩,⟨i₃.val,hi3⟩,
      ⟨j₁.val-1,by omega⟩,⟨j₂.val-1,by omega⟩,⟨j₃.val-1,by omega⟩,
      h12,h23,?_,?_,hA13,hA21,hA32⟩
    · change j₁.val-1 < j₂.val-1; omega
    · change j₂.val-1 < j₃.val-1; omega
  · have hi1 : a+1 ≤ i₁.val := by omega
    have hi2 : a+1 ≤ i₂.val := by omega
    have hi3 : a+1 ≤ i₃.val := by omega
    have hb13 := negativeGlue_bottom_plus_value A B i₁ j₃ hi1 h13
    have hb21 := negativeGlue_bottom_plus_value A B i₂ j₁ hi2 h21
    have hb32 := negativeGlue_bottom_plus_value A B i₃ j₂ hi3 h32
    rcases hb13 with hh | ⟨hj3,hB13⟩
    · omega
    rcases hb21 with hh | ⟨hj1,hB21⟩
    · omega
    rcases hb32 with hh | ⟨hj2,hB32⟩
    · omega
    refine hb ⟨⟨i₁.val-(a+1),by omega⟩,⟨i₂.val-(a+1),by omega⟩,⟨i₃.val-(a+1),by omega⟩,
      ⟨j₁.val-(a+1),by omega⟩,⟨j₂.val-(a+1),by omega⟩,⟨j₃.val-(a+1),by omega⟩,
      ?_,?_,?_,?_,hB13,hB21,hB32⟩
    · change i₁.val-(a+1) < i₂.val-(a+1); omega
    · change i₂.val-(a+1) < i₃.val-(a+1); omega
    · change j₁.val-(a+1) < j₂.val-(a+1); omega
    · change j₂.val-(a+1) < j₃.val-(a+1); omega

end ASR312
