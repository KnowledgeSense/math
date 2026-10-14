import ASR312.RectangleNegativeEquivalence

namespace ASR312

theorem asr_topLeft_pure {r k : ℕ} (A : Rectangle (r+1) (k+1)) (ha : IsASR A)
    (hp : A 0 0 = .plus) (j : Fin (k+1)) (hj : j ≠ 0) : A 0 j = .zero := by
  have hm := asr_firstRow_no_minus A ha j
  by_contra hn
  have hplus : A 0 j = .plus := by cases hx : A 0 j <;> simp_all
  have hsum := row_sum_of_plus A ha 0 hp
  exact hj (noMinus_sum_le_one_unique (A 0) (asr_firstRow_no_minus A ha) (by omega) hplus hp)

abbrev CornerPlusRectangle (r k d : ℕ) :=
  {A : AvoidingRectangle (r+1) (k+1) d // A.val 0 0 = .plus}

noncomputable def cornerPlusPureEquiv (r k d : ℕ) :
    CornerPlusRectangle r k (d+1) ≃ PurePivotRectangle 0 r k d := by
  have hz : (Fin.last 0).castAdd r = (0 : Fin ((0+1)+r)) := Fin.ext rfl
  simp only [PurePivotRectangle,hz]
  have transport (R K D : ℕ) (hr : r+1 = R) (hk : k+1 = K) (hd : d+1 = D)
      (hR : 0 < R) (hK : 0 < K) :
      CornerPlusRectangle r k (d+1) ≃
        {A : AvoidingRectangle R K D // A.val ⟨0,hR⟩ ⟨0,hK⟩ = .plus ∧
          ∀ j, j ≠ ⟨0,hK⟩ → A.val ⟨0,hR⟩ j = .zero} := by
    subst R; subst K; subst D
    exact Equiv.subtypeEquivRight (fun (A : AvoidingRectangle (r+1) (k+1) (d+1)) =>
      ⟨fun h => ⟨h,asr_topLeft_pure A.val A.property.1 h⟩,And.left⟩)
  exact transport (1+r) (1+k) (1+d) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem cornerPlus_card (r k d : ℕ) : Nat.card (CornerPlusRectangle r k (d+1)) = S r k d := by
  rw [Nat.card_congr (cornerPlusPureEquiv r k d),rectanglePure_card]
  rw [squareASMCount_zero,one_mul]

abbrev RectangleCornerData (r k d : ℕ) :=
  EmptyFirstRowRectangles r (k+1) d ⊕ (CornerPlusRectangle r k d ⊕ NonemptyCornerZeroRectangle r k d)

def rectangleCornerDataBase {r k d : ℕ} (D : RectangleCornerData r k d) : AvoidingRectangle (r+1) (k+1) d :=
  D.elim (fun A => ⟨A.val,A.property.1,A.property.2.1,A.property.2.2.1⟩)
    (fun E => E.elim Subtype.val Subtype.val)

theorem rectangleCornerDataBase_injective (r k d : ℕ) :
    Function.Injective (@rectangleCornerDataBase r k d) := by
  have hep (A : EmptyFirstRowRectangles r (k+1) d) (B : CornerPlusRectangle r k d)
      (h : A.val = B.val.val) : False := by
    have hz := A.property.2.2.2 0
    rw [h,B.property] at hz
    cases hz
  have hen (A : EmptyFirstRowRectangles r (k+1) d) (B : NonemptyCornerZeroRectangle r k d)
      (h : A.val = B.val.val) : False := by
    obtain ⟨j,hj⟩ := B.property.2
    exact hj (h ▸ A.property.2.2.2 j)
  have hpn (A : CornerPlusRectangle r k d) (B : NonemptyCornerZeroRectangle r k d)
      (h : A.val = B.val) : False := by
    have hp := A.property
    rw [h,B.property.1] at hp
    cases hp
  intro D E h
  cases D with
  | inl A =>
    cases E with
    | inl B => exact congrArg Sum.inl (Subtype.ext (congrArg (fun X : AvoidingRectangle (r+1) (k+1) d => X.val) h))
    | inr E =>
      cases E with
      | inl B => exact False.elim (hep A B (congrArg (fun X : AvoidingRectangle (r+1) (k+1) d => X.val) h))
      | inr B => exact False.elim (hen A B (congrArg (fun X : AvoidingRectangle (r+1) (k+1) d => X.val) h))
  | inr D =>
    cases D with
    | inl A =>
      cases E with
      | inl B => exact False.elim (hep B A (congrArg (fun X : AvoidingRectangle (r+1) (k+1) d => X.val) h.symm))
      | inr E =>
        cases E with
        | inl B => exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext h))
        | inr B => exact False.elim (hpn A B h)
    | inr A =>
      cases E with
      | inl B => exact False.elim (hen B A (congrArg (fun X : AvoidingRectangle (r+1) (k+1) d => X.val) h.symm))
      | inr E =>
        cases E with
        | inl B => exact False.elim (hpn B A h.symm)
        | inr B => exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext h))

noncomputable def rectangleCornerEquiv (r k d : ℕ) :
    RectangleCornerData r k d ≃ AvoidingRectangle (r+1) (k+1) d := by
  classical
  apply Equiv.ofBijective rectangleCornerDataBase
  refine ⟨rectangleCornerDataBase_injective r k d,?_⟩
  intro A
  by_cases hz : ∀ j, A.val 0 j = .zero
  · exact ⟨.inl ⟨A.val,A.property.1,A.property.2.1,A.property.2.2,hz⟩,rfl⟩
  · by_cases hp : A.val 0 0 = .plus
    · exact ⟨.inr (.inl ⟨A,hp⟩),rfl⟩
    · have hzero : A.val 0 0 = .zero := by
        have hm := asr_firstRow_no_minus A.val A.property.1 0
        cases hx : A.val 0 0 <;> simp_all
      have hn : ∃ j, A.val 0 j ≠ .zero := by simpa only [not_forall] using hz
      exact ⟨.inr (.inr ⟨A,hzero,hn⟩),rfl⟩

theorem rectangleCorner_card_add (r k d : ℕ) (hd : d+1 ≤ k+1) :
    r.choose (d+1) + S r k d + Nat.card (NonemptyCornerZeroRectangle r k (d+1)) =
      S (r+1) (k+1) (d+1) := by
  classical
  have hh := Nat.card_congr (rectangleCornerEquiv r k (d+1))
  change Nat.card (EmptyFirstRowRectangles r (k+1) (d+1) ⊕
    (CornerPlusRectangle r k (d+1) ⊕ NonemptyCornerZeroRectangle r k (d+1))) = _ at hh
  rw [Nat.card_sum,Nat.card_sum,cornerPlus_card] at hh
  have hc : Nat.card (EmptyFirstRowRectangles r (k+1) (d+1)) = r.choose (d+1) := by
    rw [Nat.card_eq_fintype_card,emptyFirstRow_count r (k+1) (d+1) hd]
  rw [hc] at hh
  simpa only [Nat.card_eq_fintype_card,S,Nat.add_assoc] using hh

theorem rectangleCorner_card (r k d : ℕ) (hd : d+1 ≤ k+1) :
    Nat.card (NonemptyCornerZeroRectangle r k (d+1)) =
      S (r+1) (k+1) (d+1) - r.choose (d+1) - S r k d := by
  have hh := rectangleCorner_card_add r k d hd
  omega

end ASR312
