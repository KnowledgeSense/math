import ASR312.RectanglePivotSupport

namespace ASR312

abbrev RectanglePivotData (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k+1) :=
  EmptyColumnRectangle r k d ⊕ (Σ p : Fin d,
    PureAtRectangle (k := k) (d := d) (Fin.castLE hdr p) ⊕
      NegativeAtRectangle (d := d) (Fin.castLE hdr p) (lt_of_lt_of_le p.isLt hdk))

def rectangleAllDataBase {r k d : ℕ} {hdr : d ≤ r} {hdk : d ≤ k+1}
    (D : RectanglePivotData r k d hdr hdk) : AvoidingRectangle r (k+1) d :=
  D.elim Subtype.val (fun D => rectanglePivotDataBase D.2)

theorem rectangleAllDataBase_injective (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k+1) :
    Function.Injective (@rectangleAllDataBase r k d hdr hdk) := by
  have disjoint (A : EmptyColumnRectangle r k d)
      (B : Σ p : Fin d, PureAtRectangle (k := k) (d := d) (Fin.castLE hdr p) ⊕
        NegativeAtRectangle (d := d) (Fin.castLE hdr p) (lt_of_lt_of_le p.isLt hdk))
      (h : A.val = rectanglePivotDataBase B.2) : False := by
    have hz := A.property (Fin.castLE hdr B.1)
    rw [h,rectanglePivotDataPlus B.2] at hz
    cases hz
  intro D E h
  cases D with
  | inl A =>
    cases E with
    | inl B => exact congrArg Sum.inl (Subtype.ext h)
    | inr B => exact False.elim (disjoint A B h)
  | inr D =>
    cases E with
    | inl B => exact False.elim (disjoint B D h.symm)
    | inr E =>
      obtain ⟨p,D⟩ := D
      obtain ⟨q,E⟩ := E
      change rectanglePivotDataBase D = rectanglePivotDataBase E at h
      have hp := rectanglePivotDataPlus D
      have hq : (rectanglePivotDataBase D).val (Fin.castLE hdr q) 0 = .plus := h ▸ rectanglePivotDataPlus E
      have hpq := firstColumn_plus_unique _ (rectanglePivotDataBase D).property.1 hp hq
      have hpq' : p = q := Fin.ext (congrArg (fun i : Fin r => i.val) hpq)
      subst q
      have he := rectanglePivotDataBase_injective (Fin.castLE hdr p) _ h
      subst E
      rfl

noncomputable def rectanglePivotEquiv (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k+1)
    (hface : d < k+1 ∨ r ≤ k+1) :
    RectanglePivotData r k d hdr hdk ≃ AvoidingRectangle r (k+1) d := by
  apply Equiv.ofBijective rectangleAllDataBase
  refine ⟨rectangleAllDataBase_injective r k d hdr hdk,?_⟩
  intro A
  rcases firstColumn_shape A.val A.property.1 with hz | ⟨p,hp,_⟩
  · exact ⟨.inl ⟨A,hz⟩,rfl⟩
  · have hpk : p.val < k+1 := by
      rcases hface with hf | hf
      · exact firstColumn_pivot_lt_width A.val A.property.1 A.property.2.2 p hp (by rw [A.property.2.1]; exact hf)
      · exact lt_of_lt_of_le p.isLt hf
    have hpd : p.val < d := by
      have hh := rectangle_pivot_le_nonemptyRows A.val A.property.2.2 p hp hpk
      rw [A.property.2.1] at hh
      omega
    let q : Fin d := ⟨p.val,hpd⟩
    have hq : Fin.castLE hdr q = p := Fin.ext rfl
    rcases rectangle_pivot_cases A.val A.property.1 A.property.2.2 p hp hpk with hh | hh
    · refine ⟨.inr ⟨q,.inl ⟨A,?_,?_⟩⟩,rfl⟩
      · simpa only [hq] using hp
      · simpa only [hq] using hh
    · refine ⟨.inr ⟨q,.inr ⟨A,?_,?_⟩⟩,rfl⟩
      · simpa only [hq] using hp
      · simpa only [hq] using hh

theorem rectangle_pivot_count_sum (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k+1)
    (hface : d < k+1 ∨ r ≤ k+1) :
    S r (k+1) d = S r k d + ∑ p : Fin d,
      (Nat.card (PureAtRectangle (k := k) (d := d) (Fin.castLE hdr p)) +
        Nat.card (NegativeAtRectangle (d := d) (Fin.castLE hdr p) (lt_of_lt_of_le p.isLt hdk))) := by
  classical
  have hh := Nat.card_congr (rectanglePivotEquiv r k d hdr hdk hface)
  change Nat.card (EmptyColumnRectangle r k d ⊕ _) = _ at hh
  rw [Nat.card_sum,emptyColumn_card] at hh
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_sum] at hh
  simpa only [S,Nat.card_eq_fintype_card] using hh.symm

end ASR312
