import MainTheorems.PathCycleTuza.PathPacking
import MainTheorems.PathCycleTuza.PathParity

namespace ResearchMain.PathCycleTuza

open Tuza

def consecutiveVertex (n : ℕ) (i : Fin ((n - 1) / 2)) (d : Fin 3) : Fin n :=
  ⟨2 * i.val + d.val, by have := i.isLt; have := d.isLt; omega⟩

def consecutiveTriangle (n : ℕ) (i : Fin ((n - 1) / 2)) : Finset (Fin n) :=
  {consecutiveVertex n i 0, consecutiveVertex n i 1, consecutiveVertex n i 2}

theorem consecutive_edges (n : ℕ) (i : Fin ((n - 1) / 2)) :
    triangleEdges (consecutiveTriangle n i) =
      {s(consecutiveVertex n i 0, consecutiveVertex n i 1),
        s(consecutiveVertex n i 0, consecutiveVertex n i 2),
        s(consecutiveVertex n i 1, consecutiveVertex n i 2)} := by
  apply triangleEdges_triple
  all_goals
    intro h
    have hv := congrArg Fin.val h
    dsimp [consecutiveVertex] at hv
    omega

def consecutivePathPacking (n : ℕ) : PackingFamily (pathPower n 2) (Fin ((n - 1) / 2)) where
  triangle := consecutiveTriangle n
  clique i := by
    apply path_triple_clique
    all_goals dsimp [consecutiveVertex]; omega
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro e hei hej
    have hne : i.val ≠ j.val := (not_congr Fin.ext_iff).mp hij
    rw [consecutive_edges] at hei hej
    simp only [Finset.mem_insert, Finset.mem_singleton] at hei
    rcases hei with rfl | rfl | rfl
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at hej
      dsimp [consecutiveVertex] at hej
      omega

theorem consecutivePath_bound (n : ℕ) :
    (n - 1) / 2 ≤ packingNumber (pathPower n 2) := by
  simpa only [Fintype.card_fin] using (consecutivePathPacking n).number_bound

theorem path_two_inequality (n : ℕ) : Inequality (pathPower n 2) := by
  by_cases hn : n ≤ 3
  · rw [pathPower_complete n 2 hn]
    exact complete_inequality n
  · have hp := consecutivePath_bound n
    have hc := path_parity_cover n 2 (by omega)
    norm_num at hc
    unfold Inequality
    omega

end ResearchMain.PathCycleTuza
