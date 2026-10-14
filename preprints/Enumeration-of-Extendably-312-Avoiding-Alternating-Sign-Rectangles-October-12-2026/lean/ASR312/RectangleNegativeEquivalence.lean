import ASR312.RectangleNegativeReconstruction

namespace ASR312

abbrev NonemptyCornerZeroRectangle (r k d : ℕ) :=
  {B : AvoidingRectangle (r+1) (k+1) d // B.val 0 0 = .zero ∧ ∃ j, B.val 0 j ≠ .zero}

abbrev NegativePivotRectangle (a r k d : ℕ) :=
  {A : AvoidingRectangle ((a+1)+(r+1)) ((a+1)+(k+1)) ((a+1)+d) //
    A.val ((0 : Fin (r+1)).natAdd (a+1)) 0 = .plus ∧
    A.val ((0 : Fin (r+1)).natAdd (a+1)) ((0 : Fin (k+1)).natAdd (a+1)) = .minus}

def rectangleNegativeAssemble {a r k d : ℕ}
    (D : AvoidingASM (a+1) × NonemptyCornerZeroRectangle r k d) : NegativePivotRectangle a r k d := by
  refine ⟨⟨rectangleNegativeGlue D.1.val D.2.val.val,
    rectangleNegativeGlue_asr _ _ D.1.property.1 D.1.property.2 D.2.val.property.1 D.2.val.property.2.2
      D.2.property.2 D.2.property.1,?_,
    rectangleNegativeGlue_extendable _ _ D.1.property.1 D.1.property.2 D.2.val.property.2.2 D.2.property.1⟩,?_,?_⟩
  · rw [rectangleNegativeGlue_nonemptyRows _ _ D.1.property.1 D.1.property.2 D.2.val.property.1
      D.2.val.property.2.2 D.2.property.2 D.2.property.1,D.2.val.property.2.1]
  · have hz : (0 : Fin ((a+1)+(k+1))) = (0 : Fin (a+1)).castAdd (k+1) := Fin.ext rfl
    rw [hz]
    simp [rectangleNegativeGlue]
  · simp [rectangleNegativeGlue]

noncomputable def rectangleNegativeExtract {a r k d : ℕ} (A : NegativePivotRectangle a r k d) :
    AvoidingASM (a+1) × NonemptyCornerZeroRectangle r k d := by
  have ht := rectangleNegativeTop_valid A.val.val A.val.property.2.2 A.property.1
  have he := rectangleNegativeBottom_extendable A.val.val A.val.property.2.2 A.property.1 A.property.2
  have hb := rectangleNegativeBottom_asr A.val.val A.val.property.1 A.val.property.2.2 A.property.1 A.property.2
  have hn := rectangleNegativeBottom_nonemptyFirstRow A.val.val A.val.property.1 A.val.property.2.2 A.property.1 A.property.2
  have hz : rectangleNegativeBottom A.val.val 0 0 = .zero := by simp [rectangleNegativeBottom]
  refine ⟨⟨rectangleNegativeTop A.val.val,ht⟩,⟨⟨rectangleNegativeBottom A.val.val,hb,?_,he⟩,hz,hn⟩⟩
  have hc := rectangleNegativeGlue_nonemptyRows _ _ ht.1 ht.2 hb he hn hz
  rw [rectangle_negative_reconstruction _ A.val.property.1 A.val.property.2.2 A.property.1 A.property.2,
    A.val.property.2.1] at hc
  omega

noncomputable def rectangleNegativeEquiv (a r k d : ℕ) :
    NegativePivotRectangle a r k d ≃ AvoidingASM (a+1) × NonemptyCornerZeroRectangle r k d where
  toFun := rectangleNegativeExtract
  invFun := rectangleNegativeAssemble
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    exact rectangle_negative_reconstruction _ A.val.property.1 A.val.property.2.2 A.property.1 A.property.2
  right_inv D := by
    apply Prod.ext
    · apply Subtype.ext
      exact rectangleNegativeGlue_top _ _
    · apply Subtype.ext
      apply Subtype.ext
      exact rectangleNegativeGlue_bottom _ _ D.2.property.1

theorem rectangleNegative_card (a r k d : ℕ) :
    Nat.card (NegativePivotRectangle a r k d) =
      squareASMCount (a+1) * Nat.card (NonemptyCornerZeroRectangle r k d) := by
  classical
  rw [Nat.card_congr (rectangleNegativeEquiv a r k d),Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,squareASMCount]

end ASR312
