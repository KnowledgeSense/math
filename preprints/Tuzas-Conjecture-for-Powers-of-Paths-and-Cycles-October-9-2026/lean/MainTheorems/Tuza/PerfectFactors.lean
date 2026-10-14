import MainTheorems.Tuza.MatchingFactors
import MainTheorems.Tuza.PackingEdges
import MainTheorems.Tuza.CycleOrientation

namespace ResearchMain.Tuza

structure PerfectFactors (V F : Type*) extends MatchingFactors V F where
  perfect : ∀ i x, ∃ y, (graph i).Adj x y

namespace MatchingFactors

variable {V F : Type*}

def unionGraph (M : MatchingFactors V F) : SimpleGraph V where
  Adj x y := ∃ i, (M.graph i).Adj x y
  symm := ⟨by intro x y h; obtain ⟨i, hi⟩ := h; exact ⟨i, hi.symm⟩⟩
  loopless := ⟨by intro x h; obtain ⟨i, hi⟩ := h; exact (M.graph i).irrefl hi⟩

end MatchingFactors

namespace PerfectFactors

variable {V F : Type*} (M : PerfectFactors V F)

theorem neighbor_equiv (x : V) : Nonempty ((M.unionGraph.neighborSet x) ≃ F) := by
  classical
  let f : (M.unionGraph.neighborSet x) → F := fun y => y.property.choose
  have hf (y : M.unionGraph.neighborSet x) : (M.graph (f y)).Adj x y.val :=
    y.property.choose_spec
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro y z hyz
    apply Subtype.ext
    exact M.matching (f y) x y.val z.val (hf y) (hyz ▸ hf z)
  · intro i
    obtain ⟨y, hy⟩ := M.perfect i x
    let z : M.unionGraph.neighborSet x := ⟨y, i, hy⟩
    exact ⟨z, M.separated (f z) i x y (hf z) hy⟩

theorem degree [Fintype V] [Fintype F] [DecidableEq V] (x : V)
    [DecidableRel M.unionGraph.Adj] : M.unionGraph.degree x = Fintype.card F := by
  obtain ⟨e⟩ := M.neighbor_equiv x
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e]

theorem card_edges [Fintype V] [Fintype F] [DecidableEq V]
    [DecidableRel M.unionGraph.Adj] :
    2 * M.unionGraph.edgeFinset.card = Fintype.card V * Fintype.card F := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp_rw [M.degree]
  simp

theorem two_cycle_orientation [Finite V] (M : PerfectFactors V (Fin 2)) :
    Nonempty (CycleOrientation M.unionGraph) := by
  apply exists_cycle_orientation
  · intro x _
    obtain ⟨e⟩ := M.neighbor_equiv x
    change Nat.card (M.unionGraph.neighborSet x) = 2
    rw [Nat.card_congr e]
    simp
  · intro x
    obtain ⟨y, hy⟩ := M.perfect 0 x
    exact ⟨y, 0, hy⟩

end PerfectFactors

structure FactorDecomposition (V F : Type*) [DecidableEq V] where
  factors : PerfectFactors V F
  triangles : TriangleDecomposition (⊤ \ factors.unionGraph)

end ResearchMain.Tuza
