import ASR312.PivotEquivalences

namespace ASR312

 abbrev PlusCornerASM (n : ℕ) := {A : AvoidingASM (n+1) // A.val 0 0 = .plus}

 theorem asm_corner_plus_pure {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (hp : A 0 0 = .plus) :
    ∀ j, j ≠ 0 → A 0 j = .zero := by
  rcases row_firstColumn_structure A ha.1 ((asm_extendable_iff A ha).mpr hav) 0 hp with hh | ⟨z,u,hz0,_,hz,_⟩
  · exact hh
  · have he := asm_negative_pivot_diagonal A ha hav 0 z hp hz
    subst z
    exact False.elim (lt_irrefl _ hz0)

 def plusCornerEquiv (n : ℕ) : PlusCornerASM n ≃ PurePivotASM (0 : Fin (n+1)) where
  toFun A := ⟨A.val,A.property,asm_corner_plus_pure _ A.val.property.1 A.val.property.2 A.property⟩
  invFun A := ⟨A.val,A.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

 theorem squareASMCount_zero : squareASMCount 0 = 1 := by
  rw [← S_square]
  exact S_zero 0 0

 theorem plusCorner_card (n : ℕ) : Nat.card (PlusCornerASM n) = squareASMCount n := by
  rw [Nat.card_congr (plusCornerEquiv n),purePivot_card]
  simp [squareASMCount_zero]

 theorem asm_corner_zero_or_plus {n : ℕ} (A : AvoidingASM (n+1)) :
    A.val 0 0 = .zero ∨ A.val 0 0 = .plus := by
  have hm := firstColumn_not_minus A.val A.property.1.1 0
  cases he : A.val 0 0 <;> simp_all

 noncomputable def cornerSplitEquiv (n : ℕ) :
    AvoidingASM (n+1) ≃ ZeroCornerASM (n+1) ⊕ PlusCornerASM n := by
  classical
  exact {
    toFun := fun A => if h : A.val 0 0 = .zero then .inl ⟨A,h⟩
      else .inr ⟨A,(asm_corner_zero_or_plus A).resolve_left h⟩
    invFun := fun A => A.elim Subtype.val Subtype.val
    left_inv := fun A => by dsimp; split_ifs <;> rfl
    right_inv := fun A => by
      cases A with
      | inl A => simp [A.property]
      | inr A => simp [A.property] }

 theorem zeroCorner_card_add (n : ℕ) :
    Nat.card (ZeroCornerASM (n+1)) + squareASMCount n = squareASMCount (n+1) := by
  have he := Nat.card_congr (cornerSplitEquiv n)
  rw [Nat.card_sum,plusCorner_card] at he
  classical
  simpa only [Nat.card_eq_fintype_card,squareASMCount] using he.symm

 theorem zeroCorner_card (n : ℕ) :
    Nat.card (ZeroCornerASM (n+1)) = squareASMCount (n+1) - squareASMCount n := by
  have he := zeroCorner_card_add n
  omega

 theorem negativePivot_card_formula (a b : ℕ) :
    Nat.card (NegativePivotASM a b) =
      squareASMCount (a+1) * (squareASMCount (b+1) - squareASMCount b) := by
  rw [negativePivot_card,zeroCorner_card]

end ASR312
