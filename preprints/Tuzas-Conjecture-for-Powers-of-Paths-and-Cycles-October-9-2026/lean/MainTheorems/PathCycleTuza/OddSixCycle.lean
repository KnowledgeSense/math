import MainTheorems.PathCycleTuza.SixExtension

set_option maxHeartbeats 4000000

namespace ResearchMain.PathCycleTuza

open Tuza

def oddSixVertex (n : ℕ) (hn : 15 ≤ n) (i : Fin 4) (d : Fin 3) : Fin n :=
  ⟨(![![0, 2, n - 4], ![0, 5, n - 1], ![0, n - 5, n - 2],
      ![1, n - 5, n - 1]] i) d,
    by fin_cases i <;> fin_cases d <;> norm_num <;> omega⟩

def oddSixTriangle (n : ℕ) (hn : 15 ≤ n) (i : Fin 4) : Finset (Fin n) :=
  {oddSixVertex n hn i 0, oddSixVertex n hn i 1, oddSixVertex n hn i 2}

theorem oddSix_ordered (n : ℕ) (hn : 15 ≤ n) (i : Fin 4) :
    (oddSixVertex n hn i 0).val < (oddSixVertex n hn i 1).val ∧
      (oddSixVertex n hn i 1).val < (oddSixVertex n hn i 2).val := by
  fin_cases i <;> norm_num [oddSixVertex] <;> omega

theorem oddSix_edges (n : ℕ) (hn : 15 ≤ n) (i : Fin 4) :
    triangleEdges (oddSixTriangle n hn i) =
      {s(oddSixVertex n hn i 0, oddSixVertex n hn i 1),
        s(oddSixVertex n hn i 0, oddSixVertex n hn i 2),
        s(oddSixVertex n hn i 1, oddSixVertex n hn i 2)} := by
  have ho := oddSix_ordered n hn i
  apply triangleEdges_triple
  · exact fun h => (ne_of_lt ho.1) (congrArg Fin.val h)
  · exact fun h => (ne_of_lt (ho.1.trans ho.2)) (congrArg Fin.val h)
  · exact fun h => (ne_of_lt ho.2) (congrArg Fin.val h)

def oddSixPacking (n : ℕ) (hn : 15 ≤ n) : PackingFamily (cyclePower n 6) (Fin 4) where
  triangle := oddSixTriangle n hn
  clique i := by
    apply (cyclePower n 6).is3Clique_iff.mpr
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    all_goals
      change _ ≠ _ ∧ (Nat.dist _ _ ≤ 6 ∨ n - Nat.dist _ _ ≤ 6)
      fin_cases i <;> norm_num [oddSixVertex, Nat.dist] <;> omega
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro e hei hej
    rw [oddSix_edges] at hei hej
    simp only [Finset.mem_insert, Finset.mem_singleton] at hei
    rcases hei with rfl | rfl | rfl
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at hej
      have hne : i.val ≠ j.val := (not_congr Fin.ext_iff).mp hij
      fin_cases i <;> fin_cases j <;> norm_num [oddSixVertex] at hej <;> omega

theorem oddSix_cross (n : ℕ) (hn : 15 ≤ n) (he : n % 2 = 1)
    (p : SixIndex n) (i : Fin 4) :
    Disjoint (triangleEdges (sixTriangle n (by omega) p)) (triangleEdges (oddSixTriangle n hn i)) := by
  apply Finset.disjoint_left.mpr
  intro e hep hei
  rw [six_edges] at hep
  rw [oddSix_edges] at hei
  simp only [Finset.mem_insert, Finset.mem_singleton] at hep
  rcases hep with rfl | rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at hei
    cases p with
    | inl p =>
      obtain ⟨j, x⟩ := p
      have hx := x.isLt
      fin_cases i <;> fin_cases j <;>
        norm_num [sixVertex, sixPeriodicVertex, sixAnchor, sixMiddle, sixSpan, oddSixVertex] at hx hei <;> omega
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [sixVertex, sixBoundaryVertex, oddSixVertex] at hei <;> omega

theorem oddSixCycle_bound (n : ℕ) (hn : 15 ≤ n) (he : n % 2 = 1) :
    3 * (n - 1) ≤ 2 * packingNumber (cyclePower n 6) := by
  have h := sixExtension_bound n 4 (by omega) (oddSixPacking n hn) (oddSix_cross n hn he)
  omega

end ResearchMain.PathCycleTuza
