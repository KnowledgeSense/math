import MainTheorems.PathCycleTuza.RunNeighbors
import MainTheorems.Tuza.Constructions

namespace ResearchMain.PathCycleTuza

theorem triangular_sum (c : ℕ) : (∑ i : Fin c, (c - i.val)) = (c + 1).choose 2 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have he : (∑ i : Fin c, (c + 1 - i.val)) = (∑ i : Fin c, (c - i.val)) + c := by
      calc
        _ = ∑ i : Fin c, ((c - i.val) + 1) := by
          apply Finset.sum_congr rfl
          intro i him
          have := i.isLt
          omega
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp
    rw [he, ih]
    have hc : (c + 2).choose 2 = (c + 1).choose 2 + (c + 1) := by
      rw [show c + 2 = (c + 1) + 1 by omega, Nat.choose_succ_succ]
      simp [Nat.add_comm]
    rw [hc]
    omega

namespace CircularRuns

variable {n k : ℕ} (D : CircularRuns n k)

def withinEdges (i : Fin D.count) : Finset (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin (D.length i))).edgeFinset.image
    (Sym2.map (fun j => D.vertexEquiv ⟨i, j⟩))

abbrev CrossIndex (i : Fin D.count) := Σ a : Fin (k - D.length i), Fin (k - D.length i - a.val)

def skippedEdge (i : Fin D.count) (p : D.CrossIndex i) : Sym2 (Fin n) :=
  let ha := (D.crossCapacity i).1
  let hb := (D.crossCapacity i).2
  s(D.vertexEquiv ⟨D.previous i,
      ⟨D.length (D.previous i) - p.1.val - 1, by have := p.1.isLt; omega⟩⟩,
    D.vertexEquiv ⟨D.next i, ⟨p.2.val, by have := p.2.isLt; omega⟩⟩)

def skippedEdges (i : Fin D.count) : Finset (Sym2 (Fin n)) := Finset.univ.image (D.skippedEdge i)

def edges : Finset (Sym2 (Fin n)) :=
  Finset.univ.biUnion (fun i => D.withinEdges i ∪ D.skippedEdges i)

theorem withinEdges_card (i : Fin D.count) : (D.withinEdges i).card ≤ (D.length i).choose 2 := by
  unfold withinEdges
  calc
    _ ≤ (⊤ : SimpleGraph (Fin (D.length i))).edgeFinset.card := Finset.card_image_le
    _ = _ := by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

theorem skippedEdges_card (i : Fin D.count) : (D.skippedEdges i).card ≤ (k - D.length i + 1).choose 2 := by
  unfold skippedEdges
  calc
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = _ := by simp only [Finset.card_univ, CrossIndex, Fintype.card_sigma, Fintype.card_fin, triangular_sum]

theorem edges_card : D.edges.card ≤ ∑ i : Fin D.count, runCost k (D.length i) := by
  calc
    _ ≤ ∑ i : Fin D.count, (D.withinEdges i ∪ D.skippedEdges i).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin D.count, ((D.withinEdges i).card + (D.skippedEdges i).card) :=
      Finset.sum_le_sum (fun i _ => Finset.card_union_le _ _)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.add_le_add (D.withinEdges_card i) (D.skippedEdges_card i))

theorem withinEdge_mem (p q : D.Position) (h : p.1 = q.1)
    (hne : D.vertexEquiv p ≠ D.vertexEquiv q) : s(D.vertexEquiv p, D.vertexEquiv q) ∈ D.edges := by
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  dsimp at h
  subst j
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_union_left _ ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨s(a, b), ?_, rfl⟩
  apply SimpleGraph.mem_edgeFinset.mpr
  change a ≠ b
  intro hab
  exact hne (congrArg (fun a => D.vertexEquiv ⟨i, a⟩) hab)

theorem skippedEdge_mem (p q : D.Position) (h : D.next (D.next p.1) = q.1)
    (hb : D.length p.1 - p.2.val - 1 + q.2.val < k - D.length (D.next p.1)) :
    s(D.vertexEquiv p, D.vertexEquiv q) ∈ D.edges := by
  let i := D.next p.1
  have ha : D.length p.1 - p.2.val - 1 < k - D.length i := by dsimp [i]; omega
  let a : Fin (k - D.length i) := ⟨D.length p.1 - p.2.val - 1, ha⟩
  let b : Fin (k - D.length i - a.val) := ⟨q.2.val, by dsimp [a, i]; omega⟩
  have he : D.skippedEdge i ⟨a, b⟩ = s(D.vertexEquiv p, D.vertexEquiv q) := by
    unfold skippedEdge
    dsimp only
    apply congrArg₂ Sym2.mk
    · apply congrArg D.vertexEquiv
      have hi : D.previous i = p.1 := D.previous_middle _
      apply Sigma.ext hi
      apply (Fin.heq_ext_iff (congrArg D.length hi)).mpr
      dsimp [a]
      rw [hi]
      have := p.2.isLt
      omega
    · apply congrArg D.vertexEquiv
      apply Sigma.ext h
      apply (Fin.heq_ext_iff (congrArg D.length h)).mpr
      rfl
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_union_right _ ?_⟩
  exact Finset.mem_image.mpr ⟨⟨a, b⟩, Finset.mem_univ _, he⟩

end CircularRuns

end ResearchMain.PathCycleTuza
