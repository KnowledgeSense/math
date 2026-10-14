import MainTheorems.Tuza.PackingRestriction
import MainTheorems.Tuza.DecompositionAssembly
import MainTheorems.Tuza.EdgeRegions

namespace ResearchMain.Tuza

variable {V : Type*} [Fintype V] [DecidableEq V]

def missingCliqueEdges (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (a : Fin n ↪ V) :
    Finset (Sym2 V) := (imageGraph (⊤ : SimpleGraph (Fin n)) a).edgeFinset \ G.edgeFinset

theorem exists_near_clique_packing (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (a : Fin n ↪ V) :
    ∃ P : Finset (Finset V), Packing G P ∧
      completeCount n ≤ P.card + (missingCliqueEdges G a).card ∧ CliqueSupport a P := by
  obtain ⟨Q, hQ, hc, hs⟩ := exists_clique_packing (G := imageGraph (⊤ : SimpleGraph (Fin n)) a) a
    (fun i j hij => ⟨i, j, rfl, rfl, hij⟩)
  obtain ⟨P, hP, hPQ, hn⟩ := restrict_packing (G := G) hQ
  exact ⟨P, hP, hc ▸ hn, fun t ht e he => hs t (hPQ ht) e he⟩

theorem exists_region_near_clique_packing {K : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (a : Fin n ↪ V) (c : V → K) (A : Finset K) (ha : ∀ i, c (a i) ∈ A) :
    ∃ P : Finset (Finset V), Packing G P ∧
      completeCount n ≤ P.card + (missingCliqueEdges G a).card ∧ EdgeRegionSupport c A.sym2 P := by
  obtain ⟨P, hP, hc, hs⟩ := exists_near_clique_packing G a
  exact ⟨P, hP, hc, hs.region c A ha⟩

end ResearchMain.Tuza
