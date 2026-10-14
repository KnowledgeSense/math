import HardCoreActivityThreshold.HardCoreLaw
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Leaf deletion for arbitrary finite forests, including isolated vertices. -/
namespace HardCoreActivityThreshold
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every nonempty finite forest has a vertex with at most one neighbor. -/
theorem forest_exists_leaf [Nonempty V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ v : V, ∀ u w : V, G.Adj v u → G.Adj v w → u = w := by
  obtain ⟨v, z, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨v, ?_⟩
  have he : ∀ u, G.Adj v u → u = p.snd := by
    intro u hu
    apply hG.eq_snd_of_adj_start hp hu
    have hnot : ¬ (p.cons hu.symm).IsPath := by
      intro hc
      have hl := hmax _ _ (p.cons hu.symm) hc
      simp only [Walk.length_cons] at hl
      omega
    by_contra hn
    exact hnot (hp.cons (h := hu.symm) hn)
  intro u w hu hw
  exact (he u hu).trans (he w hw).symm

theorem forest_exists_degree_le_one [Nonempty V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ v : V, G.degree v ≤ 1 := by
  classical
  obtain ⟨v, hv⟩ := forest_exists_leaf G hG
  refine ⟨v, ?_⟩
  rw [SimpleGraph.degree, Finset.card_le_one]
  intro u hu w hw
  exact hv u w (G.mem_neighborFinset v u |>.mp hu) (G.mem_neighborFinset v w |>.mp hw)

/-- Removing a vertex strictly decreases the number of vertices. -/
theorem card_delete_vertex_lt (v : V) : Fintype.card {w : V // w ≠ v} < Fintype.card V :=
  Fintype.card_subtype_lt (x := v) (by simp)

omit [Fintype V] [DecidableEq V] in
/-- Vertex deletion preserves acyclicity. -/
theorem forest_delete_vertex_acyclic (G : SimpleGraph V) (hG : G.IsAcyclic) (v : V) :
    (G.induce {w : V | w ≠ v}).IsAcyclic := hG.induce _

omit [Fintype V] in
/-- Leaf choice inside any nonempty allowed vertex set of an arbitrary finite forest. -/
theorem forest_allowed_exists_leaf (G : SimpleGraph V) (hG : G.IsAcyclic)
    (allowed : Finset V) (hn : allowed.Nonempty) :
    ∃ v ∈ allowed, ∀ u ∈ allowed, ∀ w ∈ allowed, G.Adj v u → G.Adj v w → u = w := by
  let : Nonempty {v : V // v ∈ allowed} := ⟨⟨hn.choose, hn.choose_spec⟩⟩
  obtain ⟨v, hv⟩ := forest_exists_leaf (G.induce (allowed : Set V)) (hG.induce _)
  refine ⟨v.val, v.property, ?_⟩
  intro u hu w hw hva hvw
  exact congrArg Subtype.val (hv ⟨u, hu⟩ ⟨w, hw⟩ hva hvw)

end HardCoreActivityThreshold
