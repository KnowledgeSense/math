import MainTheorems.Chores.AllocationSplit

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem mem_pair_incident (M : TwoCheapModel A E) (a b : A) (e : E) :
    e ∈ incidentEdges M {a, b} ↔ M.Cheap a e ∨ M.Cheap b e := by
  simp only [mem_incidentEdges, Finset.mem_insert, Finset.mem_singleton, TwoCheapModel.Cheap]
  tauto

omit [DecidableEq E] in
theorem isolated_cheap_iff (M : TwoCheapModel A E) {a b v : A}
    (hiso : IsolatedPair M a b) (hv : v = a ∨ v = b) (e : E) :
    M.Cheap v e ↔ e ∈ incidentEdges M {a, b} := by
  rw [mem_pair_incident]
  rcases hv with hv | hv <;> subst v
  · exact ⟨Or.inl, fun h => (hiso e h).1⟩
  · exact ⟨Or.inr, fun h => (hiso e h).2⟩

theorem collapsed_pair_owned (M : TwoCheapModel A E) {a b : A} {f : E → A}
    (hf : ∀ e, f e ∈ collapsedAllowed M a b e) {e : E}
    (he : e ∈ incidentEdges M {a, b}) : f e = a := by
  have ht := hf e
  rw [collapsedAllowed, ite_eq_left he, Finset.mem_singleton] at ht
  exact ht

theorem collapsed_pair_subset (M : TwoCheapModel A E) {a b : A} {f : E → A}
    (hf : ∀ e, f e ∈ collapsedAllowed M a b e) :
    incidentEdges M {a, b} ⊆ bundle f a := by
  intro e he
  exact (mem_bundle f a e).mpr (collapsed_pair_owned M hf he)

theorem collapsed_outside_cheap (M : TwoCheapModel A E) {a b c : A} {f : E → A}
    (hf : ∀ e, f e ∈ collapsedAllowed M a b e) (hca : c ≠ a) {e : E}
    (he : e ∈ bundle f c) : M.Cheap c e ∧ e ∉ incidentEdges M {a, b} := by
  have howner := (mem_bundle f c e).mp he
  have hn : e ∉ incidentEdges M {a, b} := by
    intro h
    exact hca (howner.symm.trans (collapsed_pair_owned M hf h))
  have ht := hf e
  rw [collapsedAllowed, ite_eq_right hn, Finset.mem_insert, howner] at ht
  rcases ht with ht | ht
  · exact False.elim (hca ht)
  · exact ⟨(mem_endpointAllowed M c e).mp ht, hn⟩

theorem aggregate_partition (M : TwoCheapModel A E) {a b : A} {f : E → A}
    (hf : ∀ e, f e ∈ collapsedAllowed M a b e) :
    bundle f a = incidentEdges M {a, b} ∪ (bundle f a \ incidentEdges M {a, b}) := by
  rw [Finset.union_comm]
  exact (Finset.sdiff_union_of_subset (collapsed_pair_subset M hf)).symm

theorem aggregate_cheap_filter (M : TwoCheapModel A E) {a b v : A}
    (hiso : IsolatedPair M a b) (hv : v = a ∨ v = b) (X : Finset E) :
    X.filter (M.Cheap v) = X ∩ incidentEdges M {a, b} := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, isolated_cheap_iff M hiso hv]

theorem aggregate_expensive_filter (M : TwoCheapModel A E) {a b v : A}
    (hiso : IsolatedPair M a b) (hv : v = a ∨ v = b) {B X : Finset E} (hX : X ⊆ B) :
    X.filter (fun e => ¬M.Cheap v e) = X ∩ (B \ incidentEdges M {a, b}) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_sdiff, isolated_cheap_iff M hiso hv]
  constructor
  · intro he
    exact ⟨he.1, hX he.1, he.2⟩
  · intro he
    exact ⟨he.1, he.2.2⟩

end ResearchMain.Chores
