import ASR312.TripleLine

namespace ASR312

 def repairedSuffix {n : ℕ} (f : Fin n → Entry) (p : Fin n) : Fin (n-p.val) → Entry :=
  fun j => if j.val = 0 then .zero else f ⟨p.val+j.val,by omega⟩

 theorem nonzeroEntries_repairedSuffix {n : ℕ} (f : Fin n → Entry) (p b : Fin n)
    (hpb : p < b) (hb : f b = .plus) (hz : ∀ j, p < j → j ≠ b → f j = .zero) :
    nonzeroEntries (List.ofFn (repairedSuffix f p)) = [.plus] := by
  let v : Fin (n-p.val) := ⟨b.val-p.val,by have := b.isLt; change p.val < b.val at hpb; omega⟩
  have hv0 : v.val ≠ 0 := by dsimp [v]; change p.val < b.val at hpb; omega
  have he : repairedSuffix f p = (fun j => if j = v then Entry.plus else .zero) := by
    funext j
    by_cases hj : j = v
    · subst j
      have hindex : (⟨p.val+v.val,by omega⟩ : Fin n) = b := by
        apply Fin.ext
        dsimp [v]
        change p.val < b.val at hpb
        omega
      simp [repairedSuffix,hv0,hindex,hb]
    · have hne : (⟨p.val+j.val,by omega⟩ : Fin n) ≠ b := by
        intro h
        apply hj
        apply Fin.ext
        have hh := congrArg (fun x : Fin n => x.val) h
        change p.val+j.val = b.val at hh
        change j.val = b.val-p.val
        omega
      by_cases hj0 : j.val = 0
      · simp [repairedSuffix,hj0,hj]
      · have hpj : p < (⟨p.val+j.val,by omega⟩ : Fin n) := by change p.val < p.val+j.val; omega
        simp [repairedSuffix,hj0,hz _ hpj hne,hj]
  rw [he]
  exact nonzero_ofFn_single v

 def blockZero {n : ℕ} (p : Fin n) : Fin (n-p.val) := ⟨0,by have := p.isLt; omega⟩

 def repairedLowerBlock {n : ℕ} (A : Rectangle n n) (p : Fin n) : Rectangle (n-p.val) (n-p.val) :=
  fun i j => if i.val = 0 ∧ j.val = 0 then .zero else lowerBlock A p.val i j

 theorem repairedLowerBlock_first_row {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1))
    (hp : A p 0 = .plus) (hz : A p p = .minus) :
    nonzeroEntries (row (repairedLowerBlock A p) (blockZero p)) = [.plus] := by
  have he := (asm_extendable_iff A ha).mpr hav
  rcases row_firstColumn_structure A ha.1 he p hp with hsingle | ⟨z,u,hz0,hzu,hz',hu,hrest⟩
  · have hp0 : p ≠ 0 := by intro h; subst p; rw [hp] at hz; cases hz
    rw [hsingle p hp0] at hz
    cases hz
  · have hzp : z = p := asm_row_minus_unique A ha hav p hz' hz
    subst z
    have hline : row (repairedLowerBlock A p) (blockZero p) = List.ofFn (repairedSuffix (A p) p) := by
      unfold row
      congr 1
      funext j
      simp [repairedLowerBlock,blockZero,lowerBlock,repairedSuffix]
    rw [hline]
    apply nonzeroEntries_repairedSuffix (A p) p u hzu hu
    intro j hpj hju
    exact hrest j (ne_of_gt (lt_trans hz0 hpj)) (ne_of_gt hpj) hju

 theorem repairedLowerBlock_first_col {n : ℕ} (A : Rectangle n n)
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin n) (hz : A p p = .minus) :
    nonzeroEntries (col (repairedLowerBlock A p) (blockZero p)) = [.plus] := by
  obtain ⟨a,b,hap,hpb,_,hb,hrest⟩ := asm_pivot_column_triple A ha hav p hz
  have hline : col (repairedLowerBlock A p) (blockZero p) = List.ofFn (repairedSuffix (fun j => A j p) p) := by
    unfold col
    congr 1
    funext j
    simp [repairedLowerBlock,blockZero,lowerBlock,repairedSuffix]
  rw [hline]
  apply nonzeroEntries_repairedSuffix (fun j => A j p) p b hpb hb
  intro j hpj hjb
  exact hrest j (ne_of_gt (lt_trans hap hpj)) (ne_of_gt hpj) hjb

end ASR312
