import MainTheorems.PathCycleTuza.PathPacking
import MainTheorems.PathCycleTuza.PathParity

set_option maxHeartbeats 2000000

namespace ResearchMain.PathCycleTuza

open Tuza

def sixAnchor : Fin 3 → ℕ := ![2, 0, 1]
def sixSpan : Fin 3 → ℕ := ![2, 6, 6]
def sixMiddle : Fin 3 → ℕ := ![1, 3, 2]

abbrev SixPeriodicIndex (n : ℕ) := Σ i : Fin 3, Fin ((n - sixAnchor i - sixSpan i + 1) / 2)
abbrev SixIndex (n : ℕ) := SixPeriodicIndex n ⊕ Fin 2

def sixPeriodicVertex (n : ℕ) (hn : 7 ≤ n) (p : SixPeriodicIndex n) (d : Fin 3) : Fin n :=
  ⟨sixAnchor p.1 + 2 * p.2.val + (![0, sixMiddle p.1, sixSpan p.1] d), by
    obtain ⟨i, j⟩ := p
    have hj := j.isLt
    fin_cases i <;> fin_cases d <;> dsimp [sixAnchor, sixMiddle, sixSpan] at * <;> omega⟩

def sixBoundaryVertex (n : ℕ) (hn : 7 ≤ n) (i : Fin 2) (d : Fin 3) : Fin n :=
  ⟨(![![0, 1, 4], ![1, 2, 6]] i) d, by fin_cases i <;> fin_cases d <;> dsimp <;> omega⟩

def sixVertex (n : ℕ) (hn : 7 ≤ n) (p : SixIndex n) (d : Fin 3) : Fin n :=
  match p with
    | .inl i => sixPeriodicVertex n hn i d
    | .inr i => sixBoundaryVertex n hn i d

def sixTriangle (n : ℕ) (hn : 7 ≤ n) (p : SixIndex n) : Finset (Fin n) :=
  {sixVertex n hn p 0, sixVertex n hn p 1, sixVertex n hn p 2}

theorem sixVertex_ordered (n : ℕ) (hn : 7 ≤ n) (p : SixIndex n) :
    (sixVertex n hn p 0).val < (sixVertex n hn p 1).val ∧
      (sixVertex n hn p 1).val < (sixVertex n hn p 2).val := by
  cases p with
  | inl p =>
    obtain ⟨i, j⟩ := p
    fin_cases i <;> dsimp [sixVertex, sixPeriodicVertex, sixAnchor, sixMiddle, sixSpan] <;> omega
  | inr i => fin_cases i <;> dsimp [sixVertex, sixBoundaryVertex] <;> omega

theorem six_edges (n : ℕ) (hn : 7 ≤ n) (p : SixIndex n) :
    triangleEdges (sixTriangle n hn p) =
      {s(sixVertex n hn p 0, sixVertex n hn p 1),
        s(sixVertex n hn p 0, sixVertex n hn p 2),
        s(sixVertex n hn p 1, sixVertex n hn p 2)} := by
  have ho := sixVertex_ordered n hn p
  apply triangleEdges_triple
  · exact fun h => (ne_of_lt ho.1) (congrArg Fin.val h)
  · exact fun h => (ne_of_lt (ho.1.trans ho.2)) (congrArg Fin.val h)
  · exact fun h => (ne_of_lt ho.2) (congrArg Fin.val h)

theorem sixTriangles_disjoint (n : ℕ) (hn : 7 ≤ n) (p q : SixIndex n) (hpq : p ≠ q) :
    Disjoint (triangleEdges (sixTriangle n hn p)) (triangleEdges (sixTriangle n hn q)) := by
  apply Finset.disjoint_left.mpr
  intro e hep heq
  rw [six_edges] at hep heq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hep
  rcases hep with rfl | rfl | rfl
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Fin.ext_iff] at heq
    cases p with
    | inl p =>
      obtain ⟨i, x⟩ := p
      cases q with
      | inl q =>
        obtain ⟨j, y⟩ := q
        by_cases hij : i = j
        · subst j
          have hxy : x.val ≠ y.val := fun h => hpq (congrArg Sum.inl (congrArg (Sigma.mk i) (Fin.ext h)))
          fin_cases i <;> dsimp [sixVertex, sixPeriodicVertex, sixAnchor, sixMiddle, sixSpan] at heq <;> omega
        · fin_cases i <;> fin_cases j <;>
            dsimp [sixVertex, sixPeriodicVertex, sixAnchor, sixMiddle, sixSpan] at heq <;> omega
      | inr j =>
        fin_cases i <;> fin_cases j <;>
          dsimp [sixVertex, sixPeriodicVertex, sixBoundaryVertex, sixAnchor, sixMiddle, sixSpan] at heq <;> omega
    | inr i =>
      cases q with
      | inl q =>
        obtain ⟨j, y⟩ := q
        fin_cases i <;> fin_cases j <;>
          dsimp [sixVertex, sixPeriodicVertex, sixBoundaryVertex, sixAnchor, sixMiddle, sixSpan] at heq <;> omega
      | inr j =>
        have hij : i.val ≠ j.val := (not_congr Fin.ext_iff).mp (fun h => hpq (congrArg Sum.inr h))
        fin_cases i <;> fin_cases j <;> dsimp [sixVertex, sixBoundaryVertex] at heq <;> omega

def sixPathPacking (n : ℕ) (hn : 7 ≤ n) : PackingFamily (pathPower n 6) (SixIndex n) where
  triangle := sixTriangle n hn
  clique p := by
    have ho := sixVertex_ordered n hn p
    apply path_triple_clique _ _ _ ho.1 ho.2
    cases p with
    | inl p =>
      obtain ⟨i, j⟩ := p
      fin_cases i <;> dsimp [sixVertex, sixPeriodicVertex, sixAnchor, sixMiddle, sixSpan] <;> omega
    | inr i => fin_cases i <;> dsimp [sixVertex, sixBoundaryVertex] <;> omega
  disjoint := sixTriangles_disjoint n hn

theorem sixPathPacking_bound (n : ℕ) (hn : 7 ≤ n) :
    (n - 3) / 2 + (n - 5) / 2 + (n - 6) / 2 + 2 ≤ packingNumber (pathPower n 6) := by
  have h := (sixPathPacking n hn).number_bound
  simp only [SixIndex, SixPeriodicIndex, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin] at h
  simp [Fin.sum_univ_succ, sixAnchor, sixSpan] at h
  omega

theorem path_six_inequality (n : ℕ) : Inequality (pathPower n 6) := by
  by_cases hn : n ≤ 7
  · rw [pathPower_complete n 6 hn]
    exact complete_inequality n
  · have hp := sixPathPacking_bound n (by omega)
    have hc := path_parity_cover n 6 (by omega)
    norm_num at hc
    unfold Inequality
    omega

end ResearchMain.PathCycleTuza
