import ASR312.EmptyRowUniqueness
import Mathlib.Data.Finset.Powerset

namespace ASR312

abbrev EmptyFirstRowRectangles (r k d : ℕ) :=
  {A : Rectangle (r+1) k // IsASR A ∧ nonemptyRows A = d ∧
    ExtendablyAvoids312 A ∧ ∀ j, A 0 j = .zero}

noncomputable instance (r k d : ℕ) : Fintype (EmptyFirstRowRectangles r k d) := Fintype.ofFinite _

noncomputable def emptyFirstRowEquiv (r k d : ℕ) (hd : d ≤ k) :
    EmptyFirstRowRectangles r k d ≃
      ↥((Finset.univ.erase (0 : Fin (r+1))).powersetCard d) := by
  classical
  refine {
    toFun := fun A => ⟨rowSupport A.val,?_⟩
    invFun := fun s => ⟨rowSupportRectangle s.val ?_,?_,?_,?_,?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · rw [Finset.mem_powersetCard,Finset.subset_erase]
    refine ⟨⟨Finset.subset_univ _,?_⟩,?_⟩
    · rw [mem_rowSupport]
      rintro ⟨j,hj⟩
      exact hj (A.property.2.2.2 j)
    · exact (rowSupport_card A.val).trans A.property.2.1
  · exact (Finset.mem_powersetCard.mp s.property).2.le.trans hd
  · exact rowSupportRectangle_asr _ _
  · rw [rowSupportRectangle_nonemptyRows]
    exact (Finset.mem_powersetCard.mp s.property).2
  · exact rowSupportRectangle_extendable _ _
  · exact rowSupportRectangle_emptyFirstRow _ _
      (Finset.subset_erase.mp (Finset.mem_powersetCard.mp s.property).1).2
  · intro A
    apply Subtype.ext
    have hc : (rowSupport A.val).card ≤ k := by
      rw [rowSupport_card,A.property.2.1]
      exact hd
    have hz : (0 : Fin (r+1)) ∉ rowSupport A.val := by
      rw [mem_rowSupport]
      rintro ⟨j,hj⟩
      exact hj (A.property.2.2.2 j)
    change rowSupportRectangle (rowSupport A.val) hc = A.val
    apply emptyFirstRow_eq_of_rowSupport _ _ (rowSupportRectangle_asr _ hc)
      (rowSupportRectangle_extendable _ hc) (rowSupportRectangle_emptyFirstRow _ hc hz)
      A.property.1 A.property.2.2.1 A.property.2.2.2
    ext i
    rw [mem_rowSupport,rowSupportRectangle_nonempty_iff]
  · intro s
    apply Subtype.ext
    ext i
    rw [mem_rowSupport,rowSupportRectangle_nonempty_iff]

theorem emptyFirstRow_count (r k d : ℕ) (hd : d ≤ k) :
    Fintype.card (EmptyFirstRowRectangles r k d) = r.choose d := by
  classical
  rw [Fintype.card_congr (emptyFirstRowEquiv r k d hd),Fintype.card_coe,Finset.card_powersetCard]
  simp

end ASR312
