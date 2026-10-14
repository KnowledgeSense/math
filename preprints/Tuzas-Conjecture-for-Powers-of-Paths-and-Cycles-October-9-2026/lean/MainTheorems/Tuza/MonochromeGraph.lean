import MainTheorems.Tuza.GraphCovers
import MainTheorems.Tuza.Constructions

namespace ResearchMain.Tuza

variable {V : Type*}

def monochromeGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ c x = c y
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (monochromeGraph G c).Adj := by
  intro x y
  change Decidable (G.Adj x y ∧ c x = c y)
  infer_instance

theorem monochromeGraph_edges [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) :
    (monochromeGraph G c).edgeFinset = coloredCover G c := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf x y => exact (mem_coloredCover G c x y).symm

theorem monochromeGraph_covers [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) :
    Cover G (monochromeGraph G c).edgeFinset := by
  rw [monochromeGraph_edges]
  exact coloredCover_covers G c

end ResearchMain.Tuza
