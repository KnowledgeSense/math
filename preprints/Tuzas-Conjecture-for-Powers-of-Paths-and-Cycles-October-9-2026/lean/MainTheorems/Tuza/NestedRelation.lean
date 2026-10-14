import MainTheorems.Tuza.CoChain
import Mathlib.Data.Fin.Tuple.Sort

namespace ResearchMain.Tuza

theorem exists_antitone_enumeration (A : Type*) [Fintype A] (f : A → ℕ) :
    ∃ e : Fin (Fintype.card A) ≃ A, Antitone (fun i => f (e i)) := by
  classical
  let e := (Fintype.equivFin A).symm
  let q : Fin (Fintype.card A) → OrderDual ℕ := fun i => OrderDual.toDual (f (e i))
  refine ⟨(Tuple.sort q).trans e, ?_⟩
  exact Tuple.monotone_sort q

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

noncomputable def rowSet (R : A → B → Prop) (a : A) : Finset B := by
  classical
  exact Finset.univ.filter (R a)

noncomputable def columnSet (R : A → B → Prop) (b : B) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => R a b)

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
@[simp]
theorem mem_rowSet (R : A → B → Prop) (a : A) (b : B) : b ∈ rowSet R a ↔ R a b := by
  classical
  simp [rowSet]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp]
theorem mem_columnSet (R : A → B → Prop) (a : A) (b : B) : a ∈ columnSet R b ↔ R a b := by
  classical
  simp [columnSet]

theorem comparable_subset_of_card_le {X : Type*} [DecidableEq X] {s t : Finset X}
    (hn : s ⊆ t ∨ t ⊆ s) (hc : t.card ≤ s.card) : t ⊆ s := by
  rcases hn with hn | hn
  · exact (Finset.eq_of_subset_of_card_le hn hc).symm.subset
  · exact hn

omit [DecidableEq B] in
theorem nested_columns {R : A → B → Prop}
    (hn : ∀ a a', rowSet R a ⊆ rowSet R a' ∨ rowSet R a' ⊆ rowSet R a) :
    ∀ b b', columnSet R b ⊆ columnSet R b' ∨ columnSet R b' ⊆ columnSet R b := by
  classical
  intro b b'
  by_contra! hf
  obtain ⟨a, ha, ha'⟩ := Finset.not_subset.mp hf.1
  obtain ⟨a', hb, hb'⟩ := Finset.not_subset.mp hf.2
  rcases hn a a' with h | h
  · exact hb' ((mem_columnSet R a' b).mpr
      ((mem_rowSet R a' b).mp (h ((mem_rowSet R a b).mpr ((mem_columnSet R a b).mp ha)))))
  · exact ha' ((mem_columnSet R a b').mpr
      ((mem_rowSet R a b').mp (h ((mem_rowSet R a' b').mpr ((mem_columnSet R a' b').mp hb)))))

theorem exists_ferrers_ordering (R : A → B → Prop)
    (hn : ∀ a a', rowSet R a ⊆ rowSet R a' ∨ rowSet R a' ⊆ rowSet R a) :
    ∃ eA : Fin (Fintype.card A) ≃ A, ∃ eB : Fin (Fintype.card B) ≃ B,
      ∃ d : FerrersProfile (Fintype.card A) (Fintype.card B),
        ∀ i j, R (eA i) (eB j) ↔ j.val < d.degree i := by
  classical
  obtain ⟨eA, hA⟩ := exists_antitone_enumeration A (fun a => (rowSet R a).card)
  obtain ⟨eB, hB⟩ := exists_antitone_enumeration B (fun b => (columnSet R b).card)
  have hrow (i i' : Fin (Fintype.card A)) (hi : i ≤ i') :
      rowSet R (eA i') ⊆ rowSet R (eA i) :=
    comparable_subset_of_card_le (hn _ _) (hA hi)
  have hcol (j j' : Fin (Fintype.card B)) (hj : j ≤ j') :
      columnSet R (eB j') ⊆ columnSet R (eB j) :=
    comparable_subset_of_card_le (nested_columns hn _ _) (hB hj)
  let degree : Fin (Fintype.card A) → ℕ :=
    fun i => (Finset.univ.filter (fun j => R (eA i) (eB j))).card
  have hbound (i : Fin (Fintype.card A)) : degree i ≤ Fintype.card B := by
    simpa [degree] using
      Finset.card_filter_le (Finset.univ : Finset (Fin (Fintype.card B)))
        (fun j => R (eA i) (eB j))
  have hanti : Antitone degree := by
    intro i i' hi
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (mem_rowSet R _ _).mp (hrow i i' hi ((mem_rowSet R _ _).mpr hj))
  refine ⟨eA, eB, ⟨degree, hbound, hanti⟩, ?_⟩
  intro i j
  exact (Fin.lt_card_filter_univ_iff_apply_of_imp (fun k => R (eA i) (eB k))
    (fun k k' hk hh => (mem_columnSet R _ _).mp
      (hcol k' k hk ((mem_columnSet R _ _).mpr hh)))).symm

end ResearchMain.Tuza
