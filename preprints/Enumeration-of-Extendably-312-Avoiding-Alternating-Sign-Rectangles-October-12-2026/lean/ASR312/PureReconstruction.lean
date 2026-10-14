import ASR312.PivotInsert
import ASR312.RepairedASM

namespace ASR312

 def pureAssembly {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) : Rectangle (n+1) (n+1) :=
  fun i j => directSum (pivotInsert M) N (Fin.cast (by omega) i) (Fin.cast (by omega) j)

 theorem pureAssembly_asm {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (hm : IsASM M) (hn : IsASM N) :
    IsASM (pureAssembly p M N) := by
  have transport {u v : ℕ} (h : u = v) (D : Rectangle v v) (hd : IsASM D) :
      IsASM (fun i j => D (Fin.cast h i) (Fin.cast h j)) := by subst v; exact hd
  exact transport (by omega : n+1 = (p.val+1)+(n-p.val)) (directSum (pivotInsert M) N) (directSum_asm _ _ (pivotInsert_asm M hm) hn)

 theorem pureAssembly_avoids312 {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (hm : Avoids312 M) (hn : Avoids312 N) :
    Avoids312 (pureAssembly p M N) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  exact directSum_avoids312 (pivotInsert M) N (pivotInsert_avoids312 M hm) hn
    ⟨Fin.cast (by omega) i₁,Fin.cast (by omega) i₂,Fin.cast (by omega) i₃,
      Fin.cast (by omega) j₁,Fin.cast (by omega) j₂,Fin.cast (by omega) j₃,
      h12,h23,hj12,hj23,h13,h21,h32⟩

 theorem pureAssembly_upper {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (i j : Fin (n+1))
    (hi : i < p) (hj0 : 0 < j.val) (hj : j ≤ p) :
    pureAssembly p M N i j = M ⟨i.val,hi⟩ ⟨j.val-1,by change j.val ≤ p.val at hj; omega⟩ := by
  unfold pureAssembly
  rw [directSum_of_left _ _ _ _ (by change i.val < p.val+1; change i.val < p.val at hi; omega)
    (by change j.val < p.val+1; change j.val ≤ p.val at hj; omega)]
  have ei : (⟨i.val,hi⟩ : Fin p.val).castSucc = (⟨i.val,by omega⟩ : Fin (p.val+1)) := Fin.ext rfl
  have ej : (⟨j.val-1,by change j.val ≤ p.val at hj; omega⟩ : Fin p.val).succ =
      (⟨j.val,by change j.val ≤ p.val at hj; omega⟩ : Fin (p.val+1)) := by apply Fin.ext; simp; omega
  exact ei ▸ ej ▸ pivotInsert_upper M ⟨i.val,hi⟩ ⟨j.val-1,by change j.val ≤ p.val at hj; omega⟩

 theorem directSum_zero_of_opposite {a b : ℕ} (A : Rectangle a a) (B : Rectangle b b)
    (i j : Fin (a+b)) (h : (i.val < a ∧ a ≤ j.val) ∨ (a ≤ i.val ∧ j.val < a)) :
    directSum A B i j = .zero := by
  revert h
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · intro h; simp only [Fin.val_castAdd] at h; omega
  · intro _; simp [directSum]
  · intro _; simp [directSum]
  · intro h; simp only [Fin.val_natAdd] at h; omega

 theorem pureAssembly_cross {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (i j : Fin (n+1))
    (h : (i ≤ p ∧ p < j) ∨ (p < i ∧ j ≤ p)) : pureAssembly p M N i j = .zero := by
  apply directSum_zero_of_opposite
  change (i.val < p.val+1 ∧ p.val+1 ≤ j.val) ∨ (p.val+1 ≤ i.val ∧ j.val < p.val+1)
  change (i.val ≤ p.val ∧ p.val < j.val) ∨ (p.val < i.val ∧ j.val ≤ p.val) at h
  omega

 theorem pureAssembly_first_col {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (i : Fin (n+1)) :
    pureAssembly p M N i 0 = if i = p then .plus else .zero := by
  by_cases hi : i ≤ p
  · unfold pureAssembly
    rw [directSum_of_left _ _ _ _ (by change i.val < p.val+1; change i.val ≤ p.val at hi; omega)
      (by change 0 < p.val+1; omega)]
    simp only [Fin.val_cast] 
    change pivotInsert M ⟨i.val,by change i.val ≤ p.val at hi; omega⟩ 0 = _
    by_cases hip : i = p
    · subst i
      have he : (⟨p.val,by omega⟩ : Fin (p.val+1)) = Fin.last p.val := Fin.ext rfl
      simpa only [he,ite_true] using pivotInsert_last_zero M
    · have hit : i.val < p.val := by change i.val ≤ p.val at hi; have := Fin.val_ne_of_ne hip; omega
      have he : (⟨i.val,by omega⟩ : Fin (p.val+1)) = (⟨i.val,hit⟩ : Fin p.val).castSucc := Fin.ext rfl
      simpa only [he,hip,ite_false] using pivotInsert_upper_zero M ⟨i.val,hit⟩
  · have hpi : p < i := lt_of_not_ge hi
    rw [pureAssembly_cross p M N i 0 (Or.inr ⟨hpi,Fin.zero_le _⟩)]
    simp [ne_of_gt hpi]

 theorem pureAssembly_pivot_succ {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (j : Fin (n+1)) (hj : j ≠ 0) :
    pureAssembly p M N p j = .zero := by
  by_cases hjp : j ≤ p
  · unfold pureAssembly
    rw [directSum_of_left _ _ _ _ (by change p.val < p.val+1; omega)
      (by change j.val < p.val+1; change j.val ≤ p.val at hjp; omega)]
    simp only [Fin.val_cast]
    have hj0 : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj
    have hi : (⟨p.val,by omega⟩ : Fin (p.val+1)) = Fin.last p.val := Fin.ext rfl
    have he : (⟨j.val,by change j.val ≤ p.val at hjp; omega⟩ : Fin (p.val+1)) =
        (⟨j.val-1,by change j.val ≤ p.val at hjp; omega⟩ : Fin p.val).succ := by apply Fin.ext; simp; omega
    rw [hi,he,pivotInsert_last_succ]
  · exact pureAssembly_cross p M N p j (Or.inl ⟨le_rfl,lt_of_not_ge hjp⟩)

 theorem pureAssembly_lower {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) (i j : Fin (n+1)) (hi : p < i) (hj : p < j) :
    pureAssembly p M N i j = N ⟨i.val-(p.val+1),by change p.val < i.val at hi; omega⟩
      ⟨j.val-(p.val+1),by change p.val < j.val at hj; omega⟩ := by
  exact directSum_of_right _ _ _ _ (by change p.val+1 ≤ i.val; exact hi)
    (by change p.val+1 ≤ j.val; exact hj)

 def pureLowerBlock {n : ℕ} (A : Rectangle (n+1) (n+1)) (p : Fin (n+1)) :
    Rectangle (n-p.val) (n-p.val) :=
  fun i j => A ⟨p.val+1+i.val,by omega⟩ ⟨p.val+1+j.val,by omega⟩

 theorem pure_reconstruction {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ j, j ≠ 0 → A p j = .zero) :
    pureAssembly p (topBlock A p) (pureLowerBlock A p) = A := by
  funext i j
  by_cases hj0 : j = 0
  · subst j
    rw [pureAssembly_first_col]
    by_cases hip : i = p
    · simpa only [hip,ite_true] using hp.symm
    · rw [ite_eq_right_iff.mpr (fun he => False.elim (hip he))]
      have hm := firstColumn_not_minus A ha.1 i
      have hplus : A i 0 ≠ .plus := fun he => hip (firstColumn_plus_unique A ha.1 he hp)
      cases he : A i 0 <;> simp_all
  · by_cases hip : i < p
    · by_cases hjp : j ≤ p
      · rw [pureAssembly_upper p _ _ i j hip (Fin.pos_iff_ne_zero.mpr hj0) hjp]
        unfold topBlock
        congr 1
        apply Fin.ext
        simp
        have := Fin.pos_iff_ne_zero.mpr hj0
        omega
      · rw [pureAssembly_cross p _ _ i j (Or.inl ⟨le_of_lt hip,lt_of_not_ge hjp⟩)]
        exact ((asm_pivot_top_facts A ha hav p hp).1 i j hip (lt_of_not_ge hjp)).symm
    · by_cases hip' : i = p
      · subst i
        rw [pureAssembly_pivot_succ p _ _ j hj0,hpure j hj0]
      · have hpi : p < i := lt_of_le_of_ne (le_of_not_gt hip) (Ne.symm hip')
        by_cases hjp : j ≤ p
        · rw [pureAssembly_cross p _ _ i j (Or.inr ⟨hpi,hjp⟩)]
          rcases lt_or_eq_of_le hjp with hjp | rfl
          · exact (asm_below_left_zero A ha hav p hp i j hpi hjp).symm
          · exact (asm_pure_pivot_lower_zero A ha hav j hp hpure i hpi).symm
        · have hpj : p < j := lt_of_not_ge hjp
          rw [pureAssembly_lower p _ _ i j hpi hpj]
          unfold pureLowerBlock
          congr 1 <;> apply Fin.ext <;> simp
          · change p.val < i.val at hpi; omega
          · change p.val < j.val at hpj; omega

 theorem pureLowerBlock_asm {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ j, j ≠ 0 → A p j = .zero) :
    IsASM (pureLowerBlock A p) ∧ Avoids312 (pureLowerBlock A p) := by
  have transport {u v : ℕ} (h : u = v) (D : Rectangle v v)
      (hd : IsASM D ∧ Avoids312 D) :
      IsASM (fun i j => D (Fin.cast h i) (Fin.cast h j)) ∧
      Avoids312 (fun i j => D (Fin.cast h i) (Fin.cast h j)) := by subst v; exact hd
  exact transport (by omega : n-p.val = n+1-(p.val+1)) (lowerBlock A (p.val+1))
    (asm_pure_lowerBlock A ha hav p hp hpure)

 theorem pureAssembly_topBlock {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) : topBlock (pureAssembly p M N) p = M := by
  funext i j
  unfold topBlock
  rw [pureAssembly_upper p M N _ _ (by exact i.isLt) (by change 0 < j.val+1; omega)
    (by change j.val+1 ≤ p.val; omega)]
  congr 1

 theorem pureAssembly_lowerBlock {n : ℕ} (p : Fin (n+1)) (M : Rectangle p.val p.val)
    (N : Rectangle (n-p.val) (n-p.val)) : pureLowerBlock (pureAssembly p M N) p = N := by
  funext i j
  unfold pureLowerBlock
  rw [pureAssembly_lower p M N _ _ (by change p.val < p.val+1+i.val; omega)
    (by change p.val < p.val+1+j.val; omega)]
  congr 1 <;> apply Fin.ext <;> simp

end ASR312
