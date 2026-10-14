import MainTheorems.UniformMatroid

namespace ResearchMain.SIBO

variable {E : Type*} [DecidableEq E]

/-- Equally sized finite sets admit a bijection fixing their common elements. -/
theorem exists_common_fixing_equiv (A B : Finset E) (hcard : A.card = B.card) :
    ∃ e : A ≃ B, ∀ x : A, (x : E) ∈ B → (e x : E) = x := by
  classical
  let d : ↥(A \ B) ≃ ↥(B \ A) := Fintype.equivOfCardEq
    (by simpa using Finset.card_sdiff_comm hcard)
  let f : A → B := fun x => if h : (x : E) ∈ B then ⟨x, h⟩ else
    ⟨d ⟨x, Finset.mem_sdiff.mpr ⟨x.property, h⟩⟩,
      (Finset.mem_sdiff.mp (d ⟨x, Finset.mem_sdiff.mpr ⟨x.property, h⟩⟩).property).1⟩
  have hfinj : Function.Injective f := by
    intro x y h
    have hv := congrArg Subtype.val h
    by_cases hx : (x : E) ∈ B <;> by_cases hy : (y : E) ∈ B
    · simp only [f, dite_eq_left hx, dite_eq_left hy] at hv
      exact Subtype.ext hv
    · simp only [f, dite_eq_left hx, dite_eq_right hy] at hv
      have hn := (Finset.mem_sdiff.mp
        (d ⟨y, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩).property).2
      exact False.elim (hn (by rw [← hv]; exact x.property))
    · simp only [f, dite_eq_right hx, dite_eq_left hy] at hv
      have hn := (Finset.mem_sdiff.mp
        (d ⟨x, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩).property).2
      exact False.elim (hn (by rw [hv]; exact y.property))
    · simp only [f, dite_eq_right hx, dite_eq_right hy] at hv
      have heq := d.injective (Subtype.ext hv)
      exact Subtype.ext (congrArg (fun z : ↥(A \ B) => (z : E)) heq)
  have hfsurj : Function.Surjective f := by
    intro y
    by_cases hy : (y : E) ∈ A
    · refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      simp [f, y.property]
    · let x := d.symm ⟨y, Finset.mem_sdiff.mpr ⟨y.property, hy⟩⟩
      have hxB : (x : E) ∉ B := (Finset.mem_sdiff.mp x.property).2
      refine ⟨⟨x, (Finset.mem_sdiff.mp x.property).1⟩, Subtype.ext ?_⟩
      simp [f, hxB, x]
  refine ⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩
  intro x hx
  change (f x : E) = x
  simp [f, hx]

/-- Common-fixing bijections give interval orderings for the uniform matroid. -/
theorem uniformMatroid_sibo [Fintype E] (r : ℕ) (hr : r ≤ Fintype.card E) :
    IsSIBO (uniformMatroid r hr : Matroid E) := by
  classical
  intro A B hA hB
  have hAc : A.card = r := by simpa using hA
  have hBc : B.card = r := by simpa using hB
  obtain ⟨β, hβ⟩ := exists_common_fixing_equiv A B (hAc.trans hBc.symm)
  let e : Fin A.card ≃ A := (A.equivFinOfCardEq rfl).symm
  let a : Fin A.card → E := fun i => e i
  let b : Fin A.card → E := fun i => β (e i)
  let o : BasisOrders A B := {
    n := A.card
    a := a
    b := b
    a_injective := Subtype.coe_injective.comp e.injective
    b_injective := Subtype.coe_injective.comp (β.injective.comp e.injective)
    a_range := by
      ext x
      constructor
      · rintro h
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact (e i).property
      · intro hx
        exact Finset.mem_image.mpr ⟨e.symm ⟨x, hx⟩, Finset.mem_univ _, by simp [a]⟩
    b_range := by
      ext x
      constructor
      · rintro h
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
        exact (β (e i)).property
      · intro hx
        exact Finset.mem_image.mpr
          ⟨e.symm (β.symm ⟨x, hx⟩), Finset.mem_univ _, by simp [b]⟩
  }
  refine ⟨o, ?_⟩
  intro lo hi _ _
  have halign : ∀ i, o.a i ∈ B → o.a i = o.b i := by
    intro i hi
    exact (hβ (e i) hi).symm
  have hc := o.exchange_card halign lo hi
  simp only [uniformMatroid_isBase, Set.ncard_coe_finset]
  exact hc.trans hBc

end ResearchMain.SIBO
