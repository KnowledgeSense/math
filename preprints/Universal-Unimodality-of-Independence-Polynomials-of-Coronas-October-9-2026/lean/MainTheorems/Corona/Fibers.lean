import MainTheorems.Corona.Graphs
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ResearchMain.Corona

open Classical Polynomial

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def fiberEmbedding (v : V) : W ↪ V × W := ⟨fun w => (v, w), fun _ _ h => (Prod.mk.inj h).2⟩

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
theorem fiberEmbedding_apply (v : V) (w : W) : fiberEmbedding v w = (v, w) := rfl

noncomputable def attachedVertices (T : V → Finset W) : Finset (V × W) :=
  Finset.univ.biUnion (fun v => (T v).map (fiberEmbedding v))

omit [Fintype W] in
theorem mem_attachedVertices (T : V → Finset W) (v : V) (w : W) :
    (v, w) ∈ attachedVertices T ↔ w ∈ T v := by
  simp [attachedVertices, fiberEmbedding_apply]

omit [Fintype W] in
theorem attachedVertices_card (T : V → Finset W) :
    (attachedVertices T).card = ∑ v, (T v).card := by
  unfold attachedVertices
  rw [Finset.card_biUnion]
  · simp only [Finset.card_map]
  · intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    rintro ⟨w, z⟩ hw hz
    simp only [Finset.mem_map, fiberEmbedding_apply, Prod.mk.injEq] at hw hz
    obtain ⟨_, _, hu, _⟩ := hw
    obtain ⟨_, _, hv, _⟩ := hz
    exact huv (hu.trans hv.symm)

noncomputable def assemble (S : Finset V) (T : V → Finset W) : Finset (V ⊕ (V × W)) :=
  S.disjSum (attachedVertices T)

omit [Fintype W] in
theorem assemble_toLeft (S : Finset V) (T : V → Finset W) : (assemble S T).toLeft = S := by
  simp only [assemble, Finset.toLeft_disjSum]

theorem attachmentFiber_assemble (S : Finset V) (T : V → Finset W) (v : V) :
    attachmentFiber (assemble S T) v = T v := by
  ext w
  rw [mem_attachmentFiber]
  simp [assemble, mem_attachedVertices]

theorem assemble_fibers (R : Finset (V ⊕ (V × W))) :
    assemble R.toLeft (attachmentFiber R) = R := by
  ext x
  rcases x with v | ⟨v, w⟩
  · simp [assemble]
  · simp [assemble, mem_attachedVertices, mem_attachmentFiber]

omit [Fintype W] in
theorem assemble_card (S : Finset V) (T : V → Finset W) :
    (assemble S T).card = S.card + ∑ v, (T v).card := by
  rw [assemble, Finset.card_disjSum, attachedVertices_card]

theorem assemble_independent (G : SimpleGraph V) (H : SimpleGraph W)
    (S : Finset V) (T : V → Finset W) :
    (corona G H).IsIndepSet (assemble S T : Set (V ⊕ (V × W))) ↔
      G.IsIndepSet (S : Set V) ∧ (∀ v, H.IsIndepSet (T v : Set W)) ∧ ∀ v ∈ S, T v = ∅ := by
  rw [corona_independent, assemble_toLeft]
  simp only [attachmentFiber_assemble]

noncomputable def fiberChoices (H : SimpleGraph W) (S : Finset V) (v : V) : Finset (Finset W) :=
  if v ∈ S then {∅} else independentSets H

omit [Fintype V] in
theorem mem_fiberChoices (H : SimpleGraph W) (S : Finset V) (v : V) (T : Finset W) :
    T ∈ fiberChoices H S v ↔ H.IsIndepSet (T : Set W) ∧ (v ∈ S → T = ∅) := by
  by_cases hv : v ∈ S
  · simp only [fiberChoices, hv, ite_true, Finset.mem_singleton, true_implies]
    constructor
    · rintro rfl
      exact ⟨independent_empty H, rfl⟩
    · exact And.right
  · simp only [fiberChoices, hv, ite_false, mem_independentSets, false_implies, and_true]

omit [Fintype V] in
theorem fiberChoices_polynomial (H : SimpleGraph W) (S : Finset V) (v : V) :
    ∑ T ∈ fiberChoices H S v, (X : ℝ[X]) ^ T.card =
      if v ∈ S then 1 else independencePolynomial H := by
  by_cases hv : v ∈ S
  · simp [fiberChoices, hv]
  · simp only [fiberChoices, hv, ite_false, independencePolynomial]

end ResearchMain.Corona
