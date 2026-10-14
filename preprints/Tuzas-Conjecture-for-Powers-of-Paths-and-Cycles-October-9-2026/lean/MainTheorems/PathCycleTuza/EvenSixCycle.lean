import MainTheorems.PathCycleTuza.SixExtension

set_option maxHeartbeats 4000000

namespace ResearchMain.PathCycleTuza

open Tuza

def evenSixVertex (n : ℕ) (hn : 14 ≤ n) (i : Fin 6) (d : Fin 3) : Fin n :=
  ⟨(![![0, 2, n - 4], ![0, 5, n - 1], ![0, n - 6, n - 3],
      ![1, n - 5, n - 3], ![1, n - 4, n - 1], ![2, n - 3, n - 1]] i) d,
    by fin_cases i <;> fin_cases d <;> norm_num <;> omega⟩

def evenSixTriangle (n : ℕ) (hn : 14 ≤ n) (i : Fin 6) : Finset (Fin n) :=
  {evenSixVertex n hn i 0, evenSixVertex n hn i 1, evenSixVertex n hn i 2}

theorem evenSix_ordered (n : ℕ) (hn : 14 ≤ n) (i : Fin 6) :
    (evenSixVertex n hn i 0).val < (evenSixVertex n hn i 1).val ∧
      (evenSixVertex n hn i 1).val < (evenSixVertex n hn i 2).val := by
  fin_cases i <;> norm_num [evenSixVertex] <;> omega

theorem evenSix_edges (n : ℕ) (hn : 14 ≤ n) (i : Fin 6) :
    triangleEdges (evenSixTriangle n hn i) =
      {s(evenSixVertex n hn i 0, evenSixVertex n hn i 1),
        s(evenSixVertex n hn i 0, evenSixVertex n hn i 2),
        s(evenSixVertex n hn i 1, evenSixVertex n hn i 2)} := by
  have ho := evenSix_ordered n hn i
  apply triangleEdges_triple
  · exact fun h => (ne_of_lt ho.1) (congrArg Fin.val h)
  · exact fun h => (ne_of_lt (ho.1.trans ho.2)) (congrArg Fin.val h)
  · exact fun h => (ne_of_lt ho.2) (congrArg Fin.val h)

def evenSixPacking (n : ℕ) (hn : 14 ≤ n) : PackingFamily (cyclePower n 6) (Fin 6) where
  triangle := evenSixTriangle n hn
  clique i := by
    apply (cyclePower n 6).is3Clique_iff.mpr
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    all_goals
      change _ ≠ _ ∧ (Nat.dist _ _ ≤ 6 ∨ n - Nat.dist _ _ ≤ 6)
      fin_cases i <;> norm_num [evenSixVertex, Nat.dist] <;> omega
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro e hei hej
    rw [evenSix_edges] at hei hej
    simp only [Finset.mem_insert, Finset.mem_singleton] at hei
    rcases hei with rfl | rfl | rfl
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at hej
      have hne : i.val ≠ j.val := (not_congr Fin.ext_iff).mp hij
      fin_cases i <;> fin_cases j <;> norm_num [evenSixVertex] at hej <;> omega

theorem evenSix_cross (n : ℕ) (hn : 14 ≤ n) (he : n % 2 = 0)
    (p : SixIndex n) (i : Fin 6) :
    Disjoint (triangleEdges (sixTriangle n (by omega) p)) (triangleEdges (evenSixTriangle n hn i)) := by
  apply Finset.disjoint_left.mpr
  intro e hep hei
  rw [six_edges] at hep
  rw [evenSix_edges] at hei
  simp only [Finset.mem_insert, Finset.mem_singleton] at hep
  rcases hep with rfl | rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at hei
    cases p with
    | inl p =>
      obtain ⟨j, x⟩ := p
      have hx := x.isLt
      fin_cases i <;> fin_cases j <;>
        norm_num [sixVertex, sixPeriodicVertex, sixAnchor, sixMiddle, sixSpan, evenSixVertex] at hx hei <;> omega
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [sixVertex, sixBoundaryVertex, evenSixVertex] at hei <;> omega

theorem evenSixCycle_bound (n : ℕ) (hn : 14 ≤ n) (he : n % 2 = 0) :
    3 * n ≤ 2 * packingNumber (cyclePower n 6) := by
  have h := sixExtension_bound n 6 (by omega) (evenSixPacking n hn) (evenSix_cross n hn he)
  omega

end ResearchMain.PathCycleTuza
