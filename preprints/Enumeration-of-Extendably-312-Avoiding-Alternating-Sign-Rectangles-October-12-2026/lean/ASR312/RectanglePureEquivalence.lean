import ASR312.RectanglePureReconstruction

namespace ASR312

abbrev PurePivotRectangle (a r k d : ℕ) :=
  {A : AvoidingRectangle ((a+1)+r) ((a+1)+k) ((a+1)+d) //
    A.val ((Fin.last a).castAdd r) 0 = .plus ∧
    ∀ j, j ≠ 0 → A.val ((Fin.last a).castAdd r) j = .zero}

theorem rectanglePureAssembly_top {a r k : ℕ} (M : Rectangle a a) (N : Rectangle r k) :
    rectanglePureTop (blockDiagonal (pivotInsert M) N) = M := by
  funext i j
  simp [rectanglePureTop,blockDiagonal,pivotInsert_upper]

theorem rectanglePureAssembly_bottom {a r k : ℕ} (M : Rectangle a a) (N : Rectangle r k) :
    rectanglePureBottom (blockDiagonal (pivotInsert M) N) = N := by
  funext i j
  simp [rectanglePureBottom,blockDiagonal]

theorem rectanglePureAssembly_pivot {a r k : ℕ} (M : Rectangle a a) (N : Rectangle r k) :
    blockDiagonal (pivotInsert M) N ((Fin.last a).castAdd r) 0 = .plus ∧
    ∀ j, j ≠ 0 → blockDiagonal (pivotInsert M) N ((Fin.last a).castAdd r) j = .zero := by
  constructor
  · have hz : (0 : Fin ((a+1)+k)) = (0 : Fin (a+1)).castAdd k := Fin.ext rfl
    rw [hz]
    simp [blockDiagonal,pivotInsert_last_zero]
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim (h (Fin.ext rfl))
      · intro _
        simp [blockDiagonal,pivotInsert_last_succ]
    · intro _
      simp [blockDiagonal]

theorem rectanglePureAssembly_nonemptyRows {a r k : ℕ} (M : Rectangle a a) (N : Rectangle r k)
    (hm : IsASM M) (hn : IsASR N) :
    nonemptyRows (blockDiagonal (pivotInsert M) N) = (a+1) + nonemptyRows N := by
  rw [blockDiagonal_nonemptyRows _ _ (pivotInsert_asm M hm).1 hn]
  rw [(nonemptyRows_eq_rows_iff _).mpr (pivotInsert_asm M hm).2.1]

def rectanglePureAssemble {a r k d : ℕ} (D : AvoidingASM a × AvoidingRectangle r k d) :
    PurePivotRectangle a r k d :=
  ⟨⟨blockDiagonal (pivotInsert D.1.val) D.2.val,
    blockDiagonal_asr _ _ (pivotInsert_asm _ D.1.property.1).1 D.2.property.1,
    by rw [rectanglePureAssembly_nonemptyRows _ _ D.1.property.1 D.2.property.1,D.2.property.2.1],
    blockDiagonal_extendable _ _ (pivotInsert_asm _ D.1.property.1)
      (pivotInsert_avoids312 _ D.1.property.2) D.2.property.2.2⟩,
    rectanglePureAssembly_pivot _ _⟩

noncomputable def rectanglePureExtract {a r k d : ℕ} (A : PurePivotRectangle a r k d) :
    AvoidingASM a × AvoidingRectangle r k d := by
  have ht := rectanglePureTop_valid A.val.val A.val.property.2.2 A.property.1
  have hb := rectanglePureBottom_valid A.val.val A.val.property.1 A.val.property.2.2
    A.property.1 A.property.2
  refine ⟨⟨rectanglePureTop A.val.val,ht⟩,⟨rectanglePureBottom A.val.val,hb.1,?_,hb.2⟩⟩
  have hn := rectanglePureAssembly_nonemptyRows _ _ ht.1 hb.1
  rw [rectangle_pure_reconstruction _ A.val.property.1 A.val.property.2.2 A.property.1 A.property.2,
    A.val.property.2.1] at hn
  omega

noncomputable def rectanglePureEquiv (a r k d : ℕ) :
    PurePivotRectangle a r k d ≃ AvoidingASM a × AvoidingRectangle r k d where
  toFun := rectanglePureExtract
  invFun := rectanglePureAssemble
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    exact rectangle_pure_reconstruction _ A.val.property.1 A.val.property.2.2 A.property.1 A.property.2
  right_inv D := by
    apply Prod.ext
    · apply Subtype.ext
      exact rectanglePureAssembly_top _ _
    · apply Subtype.ext
      exact rectanglePureAssembly_bottom _ _

theorem rectanglePure_card (a r k d : ℕ) :
    Nat.card (PurePivotRectangle a r k d) = squareASMCount a * S r k d := by
  classical
  rw [Nat.card_congr (rectanglePureEquiv a r k d),Nat.card_prod]
  simp only [Nat.card_eq_fintype_card,squareASMCount,S]

end ASR312
