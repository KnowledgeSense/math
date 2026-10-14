import ASR312.EmptyColumn

namespace ASR312

 abbrev AvoidingRectangle (r k d : ℕ) :=
    {A : Rectangle r k // IsASR A ∧ nonemptyRows A = d ∧ ExtendablyAvoids312 A}
 abbrev EmptyColumnRectangle (r k d : ℕ) :=
    {A : AvoidingRectangle r (k+1) d // ∀ i, A.val i 0 = .zero}

 def emptyColumnEquiv (r k d : ℕ) : EmptyColumnRectangle r k d ≃ AvoidingRectangle r k d where
  toFun A := ⟨dropFirstColumn A.val.val,
    (prependZeroColumn_asr _).mp (by rw [prepend_drop _ A.property]; exact A.val.property.1),
    by rw [← prependZeroColumn_nonemptyRows,prepend_drop _ A.property]; exact A.val.property.2.1,
    dropFirstColumn_extendable _ A.val.property.2.2 A.property⟩
  invFun A := ⟨⟨prependZeroColumn A.val,(prependZeroColumn_asr _).mpr A.property.1,
    by rw [prependZeroColumn_nonemptyRows]; exact A.property.2.1,
    prependZeroColumn_extendable _ A.property.2.2⟩,by simp [prependZeroColumn]⟩
  left_inv A := by apply Subtype.ext; apply Subtype.ext; exact prepend_drop _ A.property
  right_inv A := by apply Subtype.ext; exact drop_prepend _

 theorem emptyColumn_card (r k d : ℕ) : Nat.card (EmptyColumnRectangle r k d) = S r k d := by
  classical
  rw [Nat.card_congr (emptyColumnEquiv r k d),Nat.card_eq_fintype_card]
  rfl

end ASR312
