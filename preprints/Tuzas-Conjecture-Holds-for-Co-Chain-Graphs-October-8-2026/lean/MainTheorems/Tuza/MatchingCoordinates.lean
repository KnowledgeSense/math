import MainTheorems.Tuza.FiberCopies

namespace ResearchMain.Tuza

theorem perfect_matching_coordinates {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hmatch : ∀ x y z, G.Adj x y → G.Adj x z → y = z)
    (hperfect : ∀ x, ∃ y, G.Adj x y) :
    ∃ k, Nonempty ((fiberGraph (I := Fin k) (⊤ : SimpleGraph (Fin 2))) ≃g G) := by
  classical
  let s (x : V) := (hperfect x).choose
  have hs (x : V) : G.Adj x (s x) := (hperfect x).choose_spec
  have hinv (x : V) : s (s x) = x := hmatch (s x) (s (s x)) x (hs (s x)) (hs x).symm
  let R : Setoid V := {
    r x y := x = y ∨ s x = y
    iseqv := {
      refl := fun _ => Or.inl rfl
      symm := by
        intro x y h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [← h, hinv])
      trans := by
        intro x y z hxy hyz
        rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
        · exact Or.inl (hxy.trans hyz)
        · exact Or.inr (by rw [hxy, hyz])
        · exact Or.inr (hxy.trans hyz)
        · exact Or.inl (by rw [← hyz, ← hxy, hinv]) } }
  let C := Quotient R
  let q : V → C := Quotient.mk R
  let a (c : C) : V := Quotient.out c
  have ha (c : C) : q (a c) = c := Quotient.out_eq c
  have hqs (x : V) : q (s x) = q x := Quotient.sound (Or.inr (hinv x))
  let f : C × Fin 2 → V := fun z => if z.2 = 0 then a z.1 else s (a z.1)
  have hfq (z : C × Fin 2) : q (f z) = z.1 := by
    by_cases h : z.2 = 0
    · simpa [f, h] using ha z.1
    · simpa [f, h] using (hqs (a z.1)).trans (ha z.1)
  have hfinj : Function.Injective f := by
    intro z w he
    have hc : z.1 = w.1 := (hfq z).symm.trans ((congrArg q he).trans (hfq w))
    obtain ⟨c, i⟩ := z
    obtain ⟨d, j⟩ := w
    dsimp only at hc
    subst d
    congr 1
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals simp [f] at he
    · exact False.elim ((hs (a c)).ne he)
    · exact False.elim ((hs (a c)).ne he.symm)
  have hfsur : Function.Surjective f := by
    intro x
    have he : a (q x) = x ∨ s (a (q x)) = x := Quotient.exact (ha (q x))
    rcases he with he | he
    · exact ⟨(q x, 0), by simpa [f] using he⟩
    · exact ⟨(q x, 1), by simpa [f] using he⟩
  let E : C × Fin 2 ≃ V := Equiv.ofBijective f ⟨hfinj, hfsur⟩
  have hE (z w : C × Fin 2) : G.Adj (E z) (E w) ↔ z.1 = w.1 ∧ z.2 ≠ w.2 := by
    constructor
    · intro hzw
      have he : s (f z) = f w := hmatch (f z) (s (f z)) (f w) (hs (f z)) hzw
      have hc : z.1 = w.1 := (hfq z).symm.trans ((hqs (f z)).symm.trans
        ((congrArg q he).trans (hfq w)))
      refine ⟨hc, ?_⟩
      intro hi
      exact hzw.ne (congrArg E (Prod.ext hc hi))
    · rintro ⟨hc, hi⟩
      obtain ⟨c, i⟩ := z
      obtain ⟨d, j⟩ := w
      dsimp only at hc hi
      subst d
      fin_cases i <;> fin_cases j
      all_goals try exact False.elim (hi rfl)
      · exact hs (a c)
      · exact (hs (a c)).symm
  let _ : Fintype C := Fintype.ofFinite C
  let k := Fintype.card C
  let b : Fin k ≃ C := Fintype.equivOfCardEq (by simp [k])
  let e : Fin k × Fin 2 ≃ V := (Equiv.prodCongr b (Equiv.refl _)).trans E
  refine ⟨k, ⟨{
    toEquiv := e
    map_rel_iff' := by
      intro x y
      change G.Adj (E (b x.1, x.2)) (E (b y.1, y.2)) ↔ x.1 = y.1 ∧ x.2 ≠ y.2
      rw [hE, b.injective.eq_iff] }⟩⟩

end ResearchMain.Tuza
