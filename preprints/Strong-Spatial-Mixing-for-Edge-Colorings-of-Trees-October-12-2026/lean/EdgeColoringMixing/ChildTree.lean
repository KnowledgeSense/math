import EdgeColoringMixing.RootedCounting

set_option autoImplicit false

/-! Genuine child trees and their equivalence with the original-edge branch coloring sets. -/
namespace EdgeColoringMixing.RootedCounting
open TreeGeometry
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The actual component below a neighbor after deleting the root. -/
def childComponent (r : V) (i : G.neighborSet r) :
    (G.induce {v | v ≠ r}).ConnectedComponent :=
  (G.induce {v | v ≠ r}).connectedComponentMk ⟨i.1, i.2.ne'⟩

/-- Every child object is an actual induced graph on original vertices. -/
def childGraph (r : V) (i : G.neighborSet r) : SimpleGraph (childComponent r i) :=
  (childComponent r i).toSimpleGraph

theorem childGraph_isTree (hG : G.IsTree) (r : V) (i : G.neighborSet r) :
    (childGraph r i).IsTree :=
  (hG.isAcyclic.induce {v | v ≠ r}).isTree_connectedComponent (childComponent r i)

/-- The original child vertex is the root of its descendant tree. -/
def childRoot (r : V) (i : G.neighborSet r) : childComponent r i :=
  ⟨⟨i.1, i.2.ne'⟩, rfl⟩

/-- The child graph sits inside the original graph by literal vertex inclusion. -/
def childEmbedding (r : V) (i : G.neighborSet r) : childGraph r i ↪g G where
  toFun v := v.1.1
  inj' := fun _ _ h => Subtype.ext (Subtype.ext h)
  map_rel_iff' := Iff.rfl

theorem child_vertex_branch (hG : G.IsTree) (r : V) (i : G.neighborSet r)
    (v : childComponent r i) : vertexBranch hG r v.1 = i := by
  have hcomp : (G.induce {v | v ≠ r}).connectedComponentMk v.1 =
      (G.induce {v | v ≠ r}).connectedComponentMk ⟨i.1, i.2.ne'⟩ := v.2
  exact (congrArg (neighborComponentEquiv hG r).symm hcomp).trans
    (vertexBranch_neighbor hG r i)

theorem child_mem_of_vertex_branch (hG : G.IsTree) (r : V) (i : G.neighborSet r)
    (v : {v : V // v ≠ r}) (hv : vertexBranch hG r v = i) :
    v ∈ (childComponent r i).supp := by
  apply (neighborComponentEquiv hG r).symm.injective
  exact hv.trans (vertexBranch_neighbor hG r i).symm

/-- A child edge is an actual original edge in the corresponding unique branch. -/
noncomputable def childEdgeMap (hG : G.IsTree) (r : V) (i : G.neighborSet r)
    (e : (childGraph r i).edgeSet) : BranchEdge hG r i := by
  let e' := (childEmbedding r i).toCopy.toLineGraphEmbedding e
  have hr : r ∉ e'.1 := by
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | h v w =>
      change r ∉ s(v.1.1, w.1.1)
      simp only [Sym2.mem_iff, not_or]
      exact ⟨v.1.2.symm, w.1.2.symm⟩
  refine ⟨⟨e', hr⟩, ?_⟩
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h v w =>
    exact (edgeBranch_eq_of_mem hG r ⟨e', hr⟩ v.1 (by
      change v.1.1 ∈ s(v.1.1, w.1.1)
      simp)).trans (child_vertex_branch hG r i v)

theorem childEdgeMap_injective (hG : G.IsTree) (r : V) (i : G.neighborSet r) :
    Function.Injective (childEdgeMap hG r i) := by
  intro e f hef
  exact (childEmbedding r i).toCopy.toLineGraphEmbedding.injective
    (congrArg (fun x : BranchEdge hG r i => x.1.1) hef)

theorem childEdgeMap_surjective (hG : G.IsTree) (r : V) (i : G.neighborSet r) :
    Function.Surjective (childEdgeMap hG r i) := by
  intro e
  rcases e with ⟨⟨⟨e, he⟩, hr⟩, hi⟩
  induction e using Sym2.ind with
  | h v w =>
    have hv : v ≠ r := fun h => hr (by simp [h])
    have hw : w ≠ r := fun h => hr (by simp [h])
    have hvi : vertexBranch hG r ⟨v, hv⟩ = i :=
      (edgeBranch_eq_of_mem hG r ⟨⟨s(v,w), he⟩, hr⟩ ⟨v,hv⟩ (by simp)).symm.trans hi
    have hwi : vertexBranch hG r ⟨w, hw⟩ = i :=
      (edgeBranch_eq_of_mem hG r ⟨⟨s(v,w), he⟩, hr⟩ ⟨w,hw⟩ (by simp)).symm.trans hi
    let v' : childComponent r i := ⟨⟨v,hv⟩, child_mem_of_vertex_branch hG r i ⟨v,hv⟩ hvi⟩
    let w' : childComponent r i := ⟨⟨w,hw⟩, child_mem_of_vertex_branch hG r i ⟨w,hw⟩ hwi⟩
    refine ⟨⟨s(v',w'), he⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Every branch coloring variable corresponds to an edge of the actual smaller child tree. -/
noncomputable def childEdgeEquiv (hG : G.IsTree) (r : V) (i : G.neighborSet r) :
    (childGraph r i).edgeSet ≃ BranchEdge hG r i :=
  Equiv.ofBijective _ ⟨childEdgeMap_injective hG r i, childEdgeMap_surjective hG r i⟩

noncomputable instance [Fintype V] (r : V) (i : G.neighborSet r) :
    Fintype (childComponent r i) := Fintype.ofFinite _

/-- Children have strictly fewer original vertices, so exact recursion is well founded. -/
theorem child_card_lt [Fintype V] (r : V) (i : G.neighborSet r) :
    Fintype.card (childComponent r i) < Fintype.card V := by
  classical
  apply (Fintype.card_le_of_injective
    (fun v : childComponent r i => v.1) Subtype.coe_injective).trans_lt
  exact Fintype.card_subtype_lt (x := r) (by simp)

/-- Child-edge adjacency is exactly original-edge adjacency on the branch. -/
theorem child_edge_adj_iff (hG : G.IsTree) (r : V) (i : G.neighborSet r)
    (e f : (childGraph r i).edgeSet) :
    G.lineGraph.Adj (childEdgeEquiv hG r i e).1.1 (childEdgeEquiv hG r i f).1.1 ↔
      (childGraph r i).lineGraph.Adj e f :=
  (childEmbedding r i).toCopy.toLineGraphEmbedding.map_rel_iff

/-- Incidence is preserved with the literal original endpoint. -/
theorem child_edge_mem_iff (hG : G.IsTree) (r : V) (i : G.neighborSet r)
    (e : (childGraph r i).edgeSet) (v : V) :
    v ∈ (childEdgeEquiv hG r i e).1.1.1 ↔
      ∃ w : childComponent r i, w ∈ e.1 ∧ (childEmbedding r i) w = v :=
  Sym2.mem_map

/-- Actual child-tree colorings and original-edge branch colorings are exactly equivalent. -/
noncomputable def childColoringEquivBranch (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) :
    Coloring (childGraph r i) q (fun v => F ((childEmbedding r i) v)) ≃
      BranchColoring hG r q F i := by
  let E := childEdgeEquiv hG r i
  refine
    { toFun := fun σ => ⟨fun e => σ.1 (E.symm e), ?_⟩
      invFun := fun σ => ⟨fun e => σ.1 (E e), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro e f hef
      apply σ.2.1
      apply (child_edge_adj_iff hG r i _ _).mp
      change G.lineGraph.Adj (E (E.symm e)).1.1 (E (E.symm f)).1.1
      simpa only [E.apply_symm_apply] using hef
    · intro e v hv
      have hv' : v ∈ (E (E.symm e)).1.1.1 := by simpa only [E.apply_symm_apply] using hv
      obtain ⟨w, hw, hwv⟩ := (child_edge_mem_iff hG r i (E.symm e) v).mp hv'
      rw [← hwv]
      exact σ.2.2 _ w hw
  · constructor
    · intro e f hef
      exact σ.2.1 (E e) (E f) ((child_edge_adj_iff hG r i e f).mpr hef)
    · intro e v hv
      exact σ.2.2 (E e) ((childEmbedding r i) v)
        ((child_edge_mem_iff hG r i e _).mpr ⟨v, hv, rfl⟩)
  · intro σ
    apply Subtype.ext
    funext e
    exact congrArg σ.1 (E.symm_apply_apply e)
  · intro σ
    apply Subtype.ext
    funext e
    exact congrArg σ.1 (E.apply_symm_apply e)

/-- Quantifying over root-neighbor colors is the same as avoiding that color on
all actual root-incident edges. -/
theorem root_avoid_iff (r : V) {q : ℕ} (σ : G.edgeSet → Fin q) (c : Fin q) :
    (∀ i : G.neighborSet r, σ (rootEdge r i) ≠ c) ↔
      ∀ e : G.edgeSet, r ∈ e.1 → σ e ≠ c := by
  constructor
  · intro h e he
    let i := incidentEquiv r ⟨e, he⟩
    have hi : rootEdge r i = e := congrArg Subtype.val ((incidentEquiv r).symm_apply_apply ⟨e, he⟩)
    rw [← hi]
    exact h i
  · intro h i
    exact h _ (root_mem_rootEdge r i)

/-- The parent-edge compatibility condition is precisely the child root's unused-color event. -/
theorem child_compatible_iff (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r)
    (σ : Coloring (childGraph r i) q (fun v => F ((childEmbedding r i) v))) (c : Fin q) :
    Compatible c (childColoringEquivBranch hG r q F i σ) ↔
      c ∉ F i.1 ∧ ∀ j : (childGraph r i).neighborSet (childRoot r i),
        σ.1 (rootEdge (childRoot r i) j) ≠ c := by
  rw [root_avoid_iff]
  unfold Compatible
  apply and_congr_right
  intro _
  constructor
  · intro h e he
    have hv : i.1 ∈ (childEdgeEquiv hG r i e).1.1.1 :=
      (child_edge_mem_iff hG r i e i.1).mpr ⟨childRoot r i, he, rfl⟩
    have hh := h (childEdgeEquiv hG r i e) hv
    change σ.1 ((childEdgeEquiv hG r i).symm (childEdgeEquiv hG r i e)) ≠ c at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · intro h e he
    let E := childEdgeEquiv hG r i
    have he' : i.1 ∈ (E (E.symm e)).1.1.1 := by simpa only [E.apply_symm_apply] using he
    obtain ⟨w, hw, hwi⟩ := (child_edge_mem_iff hG r i (E.symm e) i.1).mp he'
    have hwroot : w = childRoot r i := (childEmbedding r i).injective hwi
    subst w
    exact h (E.symm e) hw

/-- Feasible original colorings induce feasible actual child-tree coloring problems. -/
theorem child_coloring_nonempty (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) (i : G.neighborSet r) :
    Nonempty (Coloring (childGraph r i) q (fun v => F ((childEmbedding r i) v))) := by
  obtain ⟨σ⟩ := branch_nonempty hG r q F hfull i
  exact ⟨(childColoringEquivBranch hG r q F i).symm σ⟩

/-- Descendant availability is literally the root availability on the induced child tree. -/
theorem childAvailability_eq_rootAvailability [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) (c : Fin q) :
    childAvailability hG r q F i c =
      rootAvailability (G := childGraph r i) (childRoot r i) q
        (fun v => F ((childEmbedding r i) v)) c := by
  classical
  let E := childColoringEquivBranch hG r q F i
  have hden := Fintype.card_congr E
  have hnum : Fintype.card {σ : Coloring (childGraph r i) q
      (fun v => F ((childEmbedding r i) v)) //
        c ∉ F i.1 ∧ ∀ j : (childGraph r i).neighborSet (childRoot r i),
          σ.1 (rootEdge (childRoot r i) j) ≠ c} =
      Fintype.card {σ : BranchColoring hG r q F i // Compatible c σ} := by
    exact Fintype.card_congr (E.subtypeEquiv
      (p := fun σ => c ∉ F i.1 ∧ ∀ j : (childGraph r i).neighborSet (childRoot r i),
        σ.1 (rootEdge (childRoot r i) j) ≠ c)
      (q := Compatible c) (fun σ => (child_compatible_iff hG r q F i σ c).symm))
  unfold childAvailability rootAvailability
  rw [← hden, ← hnum]
  change _ = if c ∈ F i.1 then 0 else _
  by_cases hc : c ∈ F i.1 <;> simp [hc]

/-- Exact recursive messages on actual finite child trees, with no abstract-tree surrogate. -/
theorem rootAvailability_child_recursion [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) :
    rootAvailability (G := G) r q F = availabilityStep (F r)
      (fun j : Fin (Fintype.card (G.neighborSet r)) =>
        let i := (Fintype.equivFin (G.neighborSet r)).symm j
        rootAvailability (G := childGraph r i) (childRoot r i) q
          (fun v => F ((childEmbedding r i) v))) := by
  funext c
  rw [rootAvailability_recursion hG r q F hfull (Fintype.equivFin _).symm c]
  congr 1
  funext j b
  exact childAvailability_eq_rootAvailability hG r q F _ b

end EdgeColoringMixing.RootedCounting
