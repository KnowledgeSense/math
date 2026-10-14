import MainTheorems.Tuza.Representation
import MainTheorems.Tuza.SparseClosure
import MainTheorems.Tuza.DenseClosure
import MainTheorems.Tuza.Sharpness

namespace ResearchMain.Tuza

theorem FerrersProfile.inequality {a b : ℕ} (d : FerrersProfile a b) : Inequality d.graph := by
  by_cases ha : a = 0
  · exact d.empty_inequality (Or.inl ha)
  by_cases hb : b = 0
  · exact d.empty_inequality (Or.inr hb)
  by_cases hs : d.height (halfUp b) < halfUp a
  · exact d.sparse_inequality (by omega) (by omega) hs
  · exact d.dense_inequality (by omega) (by omega) (by omega)

theorem coChain_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsCoChain G) : coverNumber G ≤ 2 * packingNumber G :=
  coChain_of_ferrers_inequality (fun _ _ d => d.inequality) G hG

end ResearchMain.Tuza
