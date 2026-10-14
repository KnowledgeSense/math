import ASR312.RectangleCornerCounting

namespace ASR312

theorem rectangle_pivot_rows_nonempty {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus) (hk : p.val < k+1)
    (i : Fin r) (hi : i ≤ p) : ∃ j, A i j ≠ .zero := by
  rcases lt_or_eq_of_le hi with hi | rfl
  · obtain ⟨j,hj⟩ := (rectangleTopBlock_asm A he p hp hk).1.2.1 ⟨i.val,hi⟩
    exact ⟨⟨j.val+1,by omega⟩,hj⟩
  · exact ⟨0,by rw [hp]; decide⟩

theorem rectangle_pivot_le_nonemptyRows {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus) (hk : p.val < k+1) :
    p.val+1 ≤ nonemptyRows A := by
  classical
  have hs : Finset.Iic p ⊆ rowSupport A := by
    intro i hi
    rw [mem_rowSupport]
    exact rectangle_pivot_rows_nonempty A he p hp hk i (Finset.mem_Iic.mp hi)
  have hc := Finset.card_le_card hs
  rwa [Fin.card_Iic,rowSupport_card] at hc

theorem rectangle_pivot_cases {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (hk : p.val < k+1) :
    (∀ j, j ≠ 0 → A p j = .zero) ∨ A p ⟨p.val,hk⟩ = .minus := by
  rcases row_firstColumn_structure A ha he p hp with hh | ⟨z,u,_,_,hz,_,_⟩
  · exact Or.inl hh
  · have heq : z = ⟨p.val,hk⟩ := Fin.ext (rectangle_negative_pivot_diagonal A he p z hp hz).symm
    exact Or.inr (heq ▸ hz)

abbrev PureAtRectangle {r k d : ℕ} (p : Fin r) :=
  {A : AvoidingRectangle r (k+1) d // A.val p 0 = .plus ∧ ∀ j, j ≠ 0 → A.val p j = .zero}

abbrev NegativeAtRectangle {r k d : ℕ} (p : Fin r) (hk : p.val < k+1) :=
  {A : AvoidingRectangle r (k+1) d // A.val p 0 = .plus ∧ A.val p ⟨p.val,hk⟩ = .minus}

def rectanglePivotDataBase {r k d : ℕ} {p : Fin r} {hk : p.val < k+1}
    (D : PureAtRectangle (k := k) (d := d) p ⊕ NegativeAtRectangle (d := d) p hk) :
    AvoidingRectangle r (k+1) d := D.elim Subtype.val Subtype.val

theorem rectanglePivotDataPlus {r k d : ℕ} {p : Fin r} {hk : p.val < k+1}
    (D : PureAtRectangle (k := k) (d := d) p ⊕ NegativeAtRectangle (d := d) p hk) :
    (rectanglePivotDataBase D).val p 0 = .plus := by
  cases D with
  | inl A => exact A.property.1
  | inr A => exact A.property.1

theorem rectanglePivotDataBase_injective {r k d : ℕ} (p : Fin r) (hk : p.val < k+1) :
    Function.Injective (@rectanglePivotDataBase r k d p hk) := by
  have disjoint (A : PureAtRectangle (k := k) (d := d) p) (B : NegativeAtRectangle (d := d) p hk)
      (h : A.val = B.val) : False := by
    have hm : A.val.val p ⟨p.val,hk⟩ = .minus := h ▸ B.property.2
    by_cases hz : (⟨p.val,hk⟩ : Fin (k+1)) = 0
    · rw [hz,A.property.1] at hm; cases hm
    · rw [A.property.2 _ hz] at hm; cases hm
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

end ASR312
