import MainTheorems.PathCycleTuza.PathMass
import MainTheorems.PathCycleTuza.PathParity

namespace ResearchMain.PathCycleTuza

open Tuza

def boundaryDifferenceFamily : DifferenceFamily 2 7 where
  first := ![1, 2]
  second := ![3, 5]
  positive := by decide
  ordered := by decide
  bounded := by decide
  disjoint := by decide

def boundaryTriple (n : ℕ) (hn : 9 ≤ n) : Fin n × Fin n × Fin n :=
  (⟨n - 9, by omega⟩, ⟨n - 3, by omega⟩, ⟨n - 1, by omega⟩)

def boundaryTriangle (n : ℕ) (hn : 9 ≤ n) : Finset (Fin n) :=
  {(boundaryTriple n hn).1, (boundaryTriple n hn).2.1, (boundaryTriple n hn).2.2}

theorem boundary_edges (n : ℕ) (hn : 9 ≤ n) :
    triangleEdges (boundaryTriangle n hn) =
      {s((boundaryTriple n hn).1, (boundaryTriple n hn).2.1),
        s((boundaryTriple n hn).1, (boundaryTriple n hn).2.2),
        s((boundaryTriple n hn).2.1, (boundaryTriple n hn).2.2)} := by
  apply triangleEdges_triple
  all_goals
    intro h
    have hv := congrArg Fin.val h
    dsimp [boundaryTriple] at hv
    omega

theorem boundary_disjoint (n : ℕ) (hn : 9 ≤ n) (p : PathIndex n boundaryDifferenceFamily) :
    Disjoint (triangleEdges (boundaryTriangle n hn))
      (triangleEdges (pathTriangle n boundaryDifferenceFamily p)) := by
  apply Finset.disjoint_left.mpr
  intro e he hb
  have hs := pathTriangle_edge_spec n boundaryDifferenceFamily p e hb
  rw [boundary_edges] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  obtain ⟨i, x⟩ := p
  have hx := x.isLt
  rcases he with rfl | rfl | rfl
  all_goals
    fin_cases i
    all_goals
      simp only [edgeLength, edgeStart, Sym2.lift_mk] at hs
      dsimp [boundaryDifferenceFamily, DifferenceFamily.span, boundaryTriple] at hs hx
      unfold Nat.dist at hs
      omega

def boundaryPacking (n k : ℕ) (hn : 9 ≤ n) (hk : 8 ≤ k) :
    PackingFamily (pathPower n k) (Option (PathIndex n boundaryDifferenceFamily)) where
  triangle p := match p with
    | none => boundaryTriangle n hn
    | some q => pathTriangle n boundaryDifferenceFamily q
  clique p := by
    cases p with
    | none =>
      apply path_triple_clique
      all_goals dsimp [boundaryTriple]; omega
    | some q => exact (pathTriangle_clique n boundaryDifferenceFamily q).mono (pathPower_mono n (by omega))
  disjoint p q hpq := by
    cases p with
    | none =>
      cases q with
      | none => exact False.elim (hpq rfl)
      | some q => exact boundary_disjoint n hn q
    | some p =>
      cases q with
      | none => exact (boundary_disjoint n hn p).symm
      | some q =>
        exact (pathPacking n boundaryDifferenceFamily).disjoint p q
          (fun h => hpq (congrArg Option.some h))

theorem boundaryPacking_bound (n k : ℕ) (hn : 9 ≤ n) (hk : 8 ≤ k) :
    2 * n - 10 ≤ packingNumber (pathPower n k) := by
  have h := (boundaryPacking n k hn hk).number_bound
  simp only [Fintype.card_option, PathIndex, Fintype.card_sigma, Fintype.card_fin] at h
  simp [Fin.sum_univ_two, boundaryDifferenceFamily, DifferenceFamily.span] at h
  omega

theorem path_eight_or_nine (n k : ℕ) (hk : k = 8 ∨ k = 9) : Inequality (pathPower n k) := by
  by_cases hn : n ≤ k + 1
  · rw [pathPower_complete n k hn]
    exact complete_inequality n
  · have hp := boundaryPacking_bound n k (by omega) (by omega)
    have hc := path_parity_cover n k (by omega)
    have hh : k / 2 = 4 := by omega
    rw [hh] at hc
    unfold Inequality
    omega

end ResearchMain.PathCycleTuza
