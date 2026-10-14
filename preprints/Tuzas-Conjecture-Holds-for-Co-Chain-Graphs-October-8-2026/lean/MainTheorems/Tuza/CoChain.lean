import MainTheorems.Tuza.Basic

namespace ResearchMain.Tuza

variable {V : Type*}

def IsCoChain (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, G.IsClique S ∧ G.IsClique Sᶜ ∧ ∀ u ∈ S, ∀ v ∈ S,
    (∀ w ∉ S, G.Adj u w → G.Adj v w) ∨ (∀ w ∉ S, G.Adj v w → G.Adj u w)

structure FerrersProfile (a b : ℕ) where
  degree : Fin a → ℕ
  bound : ∀ i, degree i ≤ b
  antitone : Antitone degree

namespace FerrersProfile

variable {a b : ℕ}

def graph (d : FerrersProfile a b) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := match x, y with
    | .inl i, .inl j => i ≠ j
    | .inr i, .inr j => i ≠ j
    | .inl i, .inr j => j.val < d.degree i
    | .inr j, .inl i => j.val < d.degree i
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all [ne_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance (d : FerrersProfile a b) : DecidableRel d.graph.Adj := by
  intro x y
  cases x <;> cases y <;> unfold graph <;> dsimp <;> infer_instance

@[simp]
theorem adj_left (d : FerrersProfile a b) (i j : Fin a) :
    d.graph.Adj (.inl i) (.inl j) ↔ i ≠ j := Iff.rfl

@[simp]
theorem adj_right (d : FerrersProfile a b) (i j : Fin b) :
    d.graph.Adj (.inr i) (.inr j) ↔ i ≠ j := Iff.rfl

@[simp]
theorem adj_cross (d : FerrersProfile a b) (i : Fin a) (j : Fin b) :
    d.graph.Adj (.inl i) (.inr j) ↔ j.val < d.degree i := Iff.rfl

theorem graph_mono {d e : FerrersProfile a b} (h : ∀ i, d.degree i ≤ e.degree i) : d.graph ≤ e.graph := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => exact hxy
    | inr j => exact lt_of_lt_of_le hxy (h i)
  | inr j =>
    cases y with
    | inl i => exact lt_of_lt_of_le hxy (h i)
    | inr i => exact hxy

theorem isCoChain (d : FerrersProfile a b) : IsCoChain d.graph := by
  let S : Set (Fin a ⊕ Fin b) := Set.range Sum.inl
  refine ⟨S, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact fun ht => hij (congrArg Sum.inl ht)
  · intro x hx y hy hxy
    cases x with
    | inl i => exact False.elim (hx ⟨i, rfl⟩)
    | inr i =>
      cases y with
      | inl j => exact False.elim (hy ⟨j, rfl⟩)
      | inr j => exact fun ht => hxy (congrArg Sum.inr ht)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rcases le_total i j with hij | hji
    · right
      intro w hw hAdj
      cases w with
      | inl k => exact False.elim (hw ⟨k, rfl⟩)
      | inr k => exact lt_of_lt_of_le hAdj (d.antitone hij)
    · left
      intro w hw hAdj
      cases w with
      | inl k => exact False.elim (hw ⟨k, rfl⟩)
      | inr k => exact lt_of_lt_of_le hAdj (d.antitone hji)

end FerrersProfile

end ResearchMain.Tuza
