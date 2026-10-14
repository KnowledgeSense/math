import ASR312.CornerCounting

namespace ASR312

 abbrev NegativeAtASM {n : ℕ} (p : Fin (n+1)) :=
   {A : AvoidingASM (n+1) // A.val p 0 = .plus ∧ A.val p p = .minus}

 theorem negativeAt_card_zero (n : ℕ) : Nat.card (NegativeAtASM (0 : Fin (n+1))) = 0 := by
  let : IsEmpty (NegativeAtASM (0 : Fin (n+1))) := ⟨fun A => by
    have h := A.property.2
    rw [A.property.1] at h
    cases h⟩
  simp

 theorem negativeAt_card {n : ℕ} (p : Fin (n+1)) (hp : 0 < p.val) :
    Nat.card (NegativeAtASM p) = squareASMCount p.val *
      (squareASMCount (n+1-p.val) - squareASMCount (n-p.val)) := by
  obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hn : n = (a+1)+(n-p.val) := by omega
  generalize hb : n-p.val = b at hn ⊢
  subst n
  have he : p = (0 : Fin (b+1)).natAdd (a+1) := by apply Fin.ext; simpa using ha
  subst p
  change Nat.card (NegativePivotASM a b) = _
  have hs : a+1+b+1-(a+1) = b+1 := by omega
  simpa only [Fin.val_natAdd,Fin.val_zero,Nat.add_zero,hs] using negativePivot_card_formula a b

 theorem asm_pivot_cases {n : ℕ} (A : AvoidingASM (n+1)) (p : Fin (n+1))
    (hp : A.val p 0 = .plus) :
    (∀ j, j ≠ 0 → A.val p j = .zero) ∨ A.val p p = .minus := by
  rcases row_firstColumn_structure A.val A.property.1.1
    ((asm_extendable_iff A.val A.property.1).mpr A.property.2) p hp with hh | ⟨z,u,_,_,hz,_⟩
  · exact Or.inl hh
  · have he := asm_negative_pivot_diagonal A.val A.property.1 A.property.2 p z hp hz
    exact Or.inr (he ▸ hz)

 theorem asm_firstColumn_exists {n : ℕ} (A : AvoidingASM (n+1)) : ∃ p, A.val p 0 = .plus := by
  obtain ⟨p,hp⟩ := (A.property.1.2.2 0).1
  have hm := firstColumn_not_minus A.val A.property.1.1 p
  cases he : A.val p 0 <;> simp_all
  exact ⟨p,he⟩

 def pivotDataBase {n : ℕ} {p : Fin (n+1)} (D : PurePivotASM p ⊕ NegativeAtASM p) :
    AvoidingASM (n+1) := D.elim Subtype.val Subtype.val

 theorem pivotDataPlus {n : ℕ} {p : Fin (n+1)} (D : PurePivotASM p ⊕ NegativeAtASM p) :
    (pivotDataBase D).val p 0 = .plus := by
  cases D with
  | inl A => exact A.property.1
  | inr A => exact A.property.1

 theorem pivotDataBase_injective {n : ℕ} (p : Fin (n+1)) :
    Function.Injective (@pivotDataBase n p) := by
  have disjoint (A : PurePivotASM p) (B : NegativeAtASM p)
      (h : A.val = B.val) : False := by
    have hp : A.val.val p 0 = .plus := A.property.1
    have hm : A.val.val p p = .minus := h ▸ B.property.2
    by_cases hz : p = 0
    · subst p; rw [hp] at hm; cases hm
    · rw [A.property.2 p hz] at hm; cases hm
  intro D E h
  cases D with
  | inl A =>
    cases E with
    | inl B => exact congrArg Sum.inl (Subtype.ext h)
    | inr B => exact False.elim (disjoint A B h)
  | inr A =>
    cases E with
    | inl B => exact False.elim (disjoint B A h.symm)
    | inr B => exact congrArg Sum.inr (Subtype.ext h)

 noncomputable def squarePivotEquiv (n : ℕ) :
    AvoidingASM (n+1) ≃ (Σ p : Fin (n+1), PurePivotASM p ⊕ NegativeAtASM p) := by
  apply Equiv.symm
  apply Equiv.ofBijective (fun D => pivotDataBase D.2)
  constructor
  · rintro ⟨p,D⟩ ⟨q,E⟩ he
    change pivotDataBase D = pivotDataBase E at he
    have hp := pivotDataPlus D
    have hq : (pivotDataBase D).val q 0 = .plus := he ▸ pivotDataPlus E
    have hpq : p = q := firstColumn_plus_unique _ (pivotDataBase D).property.1.1 hp hq
    subst q
    have hh := pivotDataBase_injective p he
    subst E
    rfl
  · intro A
    obtain ⟨p,hp⟩ := asm_firstColumn_exists A
    rcases asm_pivot_cases A p hp with hh | hh
    · exact ⟨⟨p,.inl ⟨A,hp,hh⟩⟩,rfl⟩
    · exact ⟨⟨p,.inr ⟨A,hp,hh⟩⟩,rfl⟩

 theorem squareASMCount_pivot_sum (n : ℕ) :
    squareASMCount (n+1) = ∑ p : Fin (n+1),
      (squareASMCount p.val * squareASMCount (n-p.val) + Nat.card (NegativeAtASM p)) := by
  classical
  have he := Nat.card_congr (squarePivotEquiv n)
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at he
  simp only [Fintype.card_sum] at he
  simp only [← Nat.card_eq_fintype_card,purePivot_card] at he
  simpa only [Nat.card_eq_fintype_card,squareASMCount] using he

end ASR312
