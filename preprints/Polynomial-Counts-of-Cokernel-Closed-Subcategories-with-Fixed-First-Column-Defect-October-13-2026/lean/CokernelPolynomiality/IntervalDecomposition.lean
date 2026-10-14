import CokernelPolynomiality.ChainDimension

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CokernelPolynomiality

/-- An actual chain representation obtained as a finite direct sum of interval
representations, up to isomorphism. -/
inductive IsIntervalSum (n : ℕ) : ChainRep n → Prop
  | zero (V : ChainRep n) (h : IsZero V) : IsIntervalSum n V
  | cons (V W : ChainRep n) (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n)
      (hW : IsIntervalSum n W) (e : V ≅ biprod W (intervalRep n a b)) : IsIntervalSum n V

theorem isZero_of_vertices_zero {n : ℕ} (V : ChainRep n)
    (h : ∀ (i : (Fin (n+1))ᵒᵈ) (x : V.obj i), x=0) : IsZero V := by
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.hom_ext
  intro x
  exact h i x

/-- Finite-dimensional representations of the uniformly oriented chain
really decompose into intervals; this is not an assumed classification. -/
theorem interval_decomposition {n : ℕ} (V : ChainRep n) : IsIntervalSum n V := by
  classical
  generalize hm : totalDimension V=m
  induction m using Nat.strong_induction_on generalizing V with
  | h m ih =>
    by_cases hne : ∃ (i : (Fin (n+1))ᵒᵈ) (x : V.obj i), x ≠ 0
    · obtain ⟨s⟩ := exists_intervalSeed V hne
      let t := s.toSplitInterval
      have hlt : totalDimension (kernel t.retraction)<m := by
        rw [← hm]
        exact t.kernel_dimension_lt
      have hk := ih (totalDimension (kernel t.retraction)) hlt (kernel t.retraction) rfl
      exact .cons V (kernel t.retraction) t.a t.b t.hab t.hbn hk
        (splitKernelIso t.inclusion t.retraction t.splitting)
    · apply IsIntervalSum.zero V
      apply isZero_of_vertices_zero
      intro i x
      by_contra hx
      exact hne ⟨i,x,hx⟩

theorem CokernelSubcategory.contains_biprod_iff {n : ℕ} (C : CokernelSubcategory n)
    (X Y : ChainRep n) : C.contains (biprod X Y) ↔ C.contains X ∧ C.contains Y := by
  constructor
  · intro h
    exact ⟨C.retract_mem biprod.inl biprod.fst (by simp) h,
      C.retract_mem biprod.inr biprod.snd (by simp) h⟩
  · rintro ⟨hX,hY⟩
    exact C.biprod_mem hX hY

theorem CokernelSubcategory.contains_isZero {n : ℕ} (C : CokernelSubcategory n)
    {V : ChainRep n} (hV : IsZero V) : C.contains V :=
  C.iso_closed hV.isoZero.symm C.zero_mem

/-- Full additive retract-closed subcategories are determined by which actual
interval representations they contain. -/
theorem CokernelSubcategory.ext_intervals {n : ℕ} {C D : CokernelSubcategory n}
    (h : ∀ a b, a ≤ b → b ≤ n →
      (C.contains (intervalRep n a b) ↔ D.contains (intervalRep n a b))) : C=D := by
  apply CokernelSubcategory.ext
  intro V
  induction interval_decomposition V with
  | zero V hV => exact iff_of_true (C.contains_isZero hV) (D.contains_isZero hV)
  | cons V W a b hab hbn _ e ih =>
    have hC : C.contains V ↔ C.contains (biprod W (intervalRep n a b)) :=
      ⟨C.iso_closed e,C.iso_closed e.symm⟩
    have hD : D.contains V ↔ D.contains (biprod W (intervalRep n a b)) :=
      ⟨D.iso_closed e,D.iso_closed e.symm⟩
    rw [hC,hD,C.contains_biprod_iff,D.contains_biprod_iff,ih,h a b hab hbn]

end CokernelPolynomiality
