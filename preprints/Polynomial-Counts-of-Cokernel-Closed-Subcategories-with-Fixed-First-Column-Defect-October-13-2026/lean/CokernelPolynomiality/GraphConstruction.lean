import CokernelPolynomiality.GraphExtraction
import Mathlib.Order.Preorder.Finite

namespace CokernelPolynomiality
noncomputable section

variable {i m : ℕ}

 def vertexEquiv (i m : ℕ) : Vertex i m ≃ Option (Fin i ⊕ Fin m) where
  toFun
    | .root => none
    | .exceptional j => some (.inl j)
    | .regular t => some (.inr t)
  invFun
    | none => .root
    | some (.inl j) => .exceptional j
    | some (.inr t) => .regular t
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; cases v with
    | none => rfl
    | some v => cases v <;> rfl

 theorem card_vertex (i m : ℕ) : Fintype.card (Vertex i m) = i+m+1 := by
  rw [Fintype.card_congr (vertexEquiv i m)]
  simp

 theorem Code.root_le (c : Code i m) :
    let _ := codeOrder c.d
    ∀ v : Vertex i m, .root ≤ v := by
  let _ := codeOrder c.d
  change ∀ v : Vertex i m, .root ≤ v
  intro v
  cases v with
  | root => exact le_rfl
  | exceptional j => exact le_of_lt (root_lt_exceptional c.d j)
  | regular t => exact le_of_lt (root_lt_regular c.d t)

 def Code.indexIso (c : Code i m) :
    @OrderIso (Fin (i+m+1)) (Vertex i m) inferInstance (codeOrder c.d).toLE := by
  let _ := codeOrder c.d
  exact Fintype.orderIsoFinOfCardEq _ (card_vertex i m)

 def Code.vertexIndex (c : Code i m) (v : Vertex i m) : Fin (i+m+1) := by
  let _ := codeOrder c.d
  exact c.indexIso.symm v

 theorem Code.indexIso_vertexIndex (c : Code i m) (v : Vertex i m) :
    c.indexIso (c.vertexIndex v) = v := by
  let _ := codeOrder c.d
  exact c.indexIso.apply_symm_apply v

 theorem Code.vertexIndex_indexIso (c : Code i m) (v : Fin (i+m+1)) :
    c.vertexIndex (c.indexIso v) = v := by
  let _ := codeOrder c.d
  exact c.indexIso.symm_apply_apply v

 theorem Code.indexIso_zero (c : Code i m) : c.indexIso 0 = .root := by
  let _ := codeOrder c.d
  apply le_antisymm
  · have hh := c.indexIso.monotone (Fin.zero_le (c.indexIso.symm .root))
    simpa using hh
  · exact c.root_le _

 def Code.finiteGraph (c : Code i m) : SimpleGraph (Fin (i+m+1)) :=
  (codeGraph c.y c.epsilon).comap c.indexIso

 theorem Code.finiteGraph_neighbors (c : Code i m) :
    rootNeighbors c.finiteGraph = Finset.univ.image (fun t : Fin m => c.vertexIndex (.regular t)) := by
  classical
  let _ := codeOrder c.d
  ext v
  rw [mem_rootNeighbors]
  change (codeGraph c.y c.epsilon).Adj (c.indexIso 0) (c.indexIso v) ↔ _
  rw [c.indexIso_zero]
  constructor
  · intro hv
    cases he : c.indexIso v with
    | root => simp [he,codeGraph] at hv
    | exceptional j => simp [he,codeGraph,codeAdj] at hv
    | regular t =>
      apply Finset.mem_image.mpr
      refine ⟨t,Finset.mem_univ _,?_⟩
      rw [← he,c.vertexIndex_indexIso]
  · intro hv
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hv
    rw [c.indexIso_vertexIndex]
    trivial

 theorem Code.finiteGraph_neighbors_card (c : Code i m) :
    (rootNeighbors c.finiteGraph).card = m := by
  classical
  let _ := codeOrder c.d
  rw [c.finiteGraph_neighbors,Finset.card_image_of_injective]
  · simp
  · intro s t hst
    exact Vertex.regular.inj (c.indexIso.symm.injective hst)

 def Code.toGraphModel (c : Code i m) (hc : c.IsAdmissible) : GraphModel i m where
  graph := c.finiteGraph
  admissible := by
    let _ := codeOrder c.d
    exact admissible_comap _ hc _ c.indexIso.strictMono
  neighbors_card := c.finiteGraph_neighbors_card

 theorem Code.toGraphModel_beta (c : Code i m) (hc : c.IsAdmissible) (t : Fin m) :
    (c.toGraphModel hc).beta t = c.vertexIndex (.regular t) := by
  let _ := codeOrder c.d
  let f : Fin m ↪o Fin (i+m+1) := OrderEmbedding.ofStrictMono
    (fun t => c.vertexIndex (.regular t))
    (fun s t h => c.indexIso.symm.strictMono ((regular_lt_regular c.d s t).mpr h))
  have hh : f = (rootNeighbors c.finiteGraph).orderEmbOfFin c.finiteGraph_neighbors_card := by
    apply Finset.orderEmbOfFin_unique'
    intro t
    rw [c.finiteGraph_neighbors]
    exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩
  exact (congrArg (fun f : Fin m ↪o Fin (i+m+1) => f t) hh).symm

 theorem Code.toGraphModel_alpha (c : Code i m) (hc : c.IsAdmissible) (j : Fin i) :
    (c.toGraphModel hc).alpha j = c.vertexIndex (.exceptional j) := by
  let _ := codeOrder c.d
  let f : Fin i ↪o Fin (i+m+1) := OrderEmbedding.ofStrictMono
    (fun j => c.vertexIndex (.exceptional j))
    (fun j k h => c.indexIso.symm.strictMono ((exceptional_lt_exceptional c.d c.monotone_d j k).mpr h))
  have hh : f = (rootExceptions c.finiteGraph).orderEmbOfFin (c.toGraphModel hc).exceptions_card := by
    apply Finset.orderEmbOfFin_unique'
    intro j
    apply (mem_rootExceptions _ _).mpr
    constructor
    · intro hz
      have h := congrArg c.indexIso hz
      change c.indexIso (c.vertexIndex (.exceptional j)) = c.indexIso 0 at h
      simp only [c.indexIso_vertexIndex,c.indexIso_zero] at h
      cases h
    · change ¬(codeGraph c.y c.epsilon).Adj (c.indexIso 0)
        (c.indexIso (c.vertexIndex (.exceptional j)))
      rw [c.indexIso_vertexIndex,c.indexIso_zero]
      simp [codeGraph,codeAdj]
  exact (congrArg (fun f : Fin i ↪o Fin (i+m+1) => f j) hh).symm

end
end CokernelPolynomiality
