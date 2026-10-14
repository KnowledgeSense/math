import ASR312.NegativeReconstruction
import Mathlib.SetTheory.Cardinal.Finite

namespace ASR312

 abbrev AvoidingASM (n : ℕ) := {A : Rectangle n n // IsASM A ∧ Avoids312 A}
 abbrev PurePivotASM {n : ℕ} (p : Fin (n+1)) :=
   {A : AvoidingASM (n+1) // A.val p 0 = .plus ∧ ∀ j, j ≠ 0 → A.val p j = .zero}
 abbrev ZeroCornerASM (n : ℕ) [NeZero n] := {A : AvoidingASM n // A.val 0 0 = .zero}
 abbrev NegativePivotASM (a b : ℕ) :=
   {A : AvoidingASM ((a+1)+(b+1)) //
     A.val ((0 : Fin (b+1)).natAdd (a+1)) 0 = .plus ∧
     A.val ((0 : Fin (b+1)).natAdd (a+1)) ((0 : Fin (b+1)).natAdd (a+1)) = .minus}

 def purePivotEquiv {n : ℕ} (p : Fin (n+1)) :
    PurePivotASM p ≃ AvoidingASM p.val × AvoidingASM (n-p.val) where
  toFun A := (⟨topBlock A.val.val p,asm_pivot_topBlock _ A.val.property.1 A.val.property.2 p A.property.1⟩,
    ⟨pureLowerBlock A.val.val p,pureLowerBlock_asm _ A.val.property.1 A.val.property.2 p A.property.1 A.property.2⟩)
  invFun MN := ⟨⟨pureAssembly p MN.1.val MN.2.val,
    pureAssembly_asm p _ _ MN.1.property.1 MN.2.property.1,
    pureAssembly_avoids312 p _ _ MN.1.property.2 MN.2.property.2⟩,
    by simp [pureAssembly_first_col],fun j hj => pureAssembly_pivot_succ p _ _ j hj⟩
  left_inv A := by
    apply Subtype.ext; apply Subtype.ext
    exact pure_reconstruction _ A.val.property.1 A.val.property.2 p A.property.1 A.property.2
  right_inv MN := by
    apply Prod.ext <;> apply Subtype.ext
    · exact pureAssembly_topBlock p _ _
    · exact pureAssembly_lowerBlock p _ _

 def negativePivotEquiv (a b : ℕ) :
    NegativePivotASM a b ≃ AvoidingASM (a+1) × ZeroCornerASM (b+1) where
  toFun A := (⟨negativeTopBlock A.val.val,negativeTopBlock_asm _ A.val.property.1 A.val.property.2 A.property.1⟩,
    ⟨⟨negativeLowerBlock A.val.val,negativeLowerBlock_asm _ A.val.property.1 A.val.property.2 A.property.1 A.property.2⟩,
      negativeLowerBlock_corner A.val.val⟩)
  invFun MN := ⟨⟨negativeGlue MN.1.val MN.2.val.val,
    negativeGlue_asm _ _ MN.1.property.1 MN.2.val.property.1 MN.2.property,
    negativeGlue_avoids312 _ _ MN.1.property.2 MN.2.val.property.2⟩,by
      have h0 : (0 : Fin ((a+1)+(b+1))) = (0 : Fin (a+1)).castAdd (b+1) := Fin.ext rfl
      constructor
      · rw [h0]; simp [negativeGlue]
      · simp [negativeGlue]⟩
  left_inv A := by
    apply Subtype.ext; apply Subtype.ext
    exact negative_reconstruction _ A.val.property.1 A.val.property.2 A.property.1 A.property.2
  right_inv MN := by
    apply Prod.ext
    · apply Subtype.ext; exact negativeGlue_topBlock _ _
    · apply Subtype.ext; apply Subtype.ext
      exact negativeGlue_lowerBlock _ _ MN.2.property

 theorem purePivot_card {n : ℕ} (p : Fin (n+1)) :
    Nat.card (PurePivotASM p) = squareASMCount p.val * squareASMCount (n-p.val) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (purePivotEquiv p),Fintype.card_prod]
  rfl

 theorem negativePivot_card (a b : ℕ) :
    Nat.card (NegativePivotASM a b) = squareASMCount (a+1) * Nat.card (ZeroCornerASM (b+1)) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (negativePivotEquiv a b),Fintype.card_prod,
    Nat.card_eq_fintype_card]
  rfl

end ASR312
