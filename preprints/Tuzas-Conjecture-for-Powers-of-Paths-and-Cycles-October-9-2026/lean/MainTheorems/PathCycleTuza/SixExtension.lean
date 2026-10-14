import MainTheorems.PathCycleTuza.SixPath

namespace ResearchMain.PathCycleTuza

open Tuza

theorem pathPower_le_cyclePower (n k : ℕ) : pathPower n k ≤ cyclePower n k := by
  intro x y h
  exact ⟨h.1, Or.inl h.2⟩

def combinePacking {V I J : Type*} [DecidableEq V] {G : SimpleGraph V}
    (P : PackingFamily G I) (Q : PackingFamily G J)
    (hc : ∀ i j, Disjoint (triangleEdges (P.triangle i)) (triangleEdges (Q.triangle j))) :
    PackingFamily G (I ⊕ J) where
  triangle := Sum.elim P.triangle Q.triangle
  clique p := by cases p with
    | inl i => exact P.clique i
    | inr j => exact Q.clique j
  disjoint p q hpq := by
    cases p with
    | inl i =>
      cases q with
      | inl j => exact P.disjoint i j (fun h => hpq (congrArg Sum.inl h))
      | inr j => exact hc i j
    | inr i =>
      cases q with
      | inl j => exact (hc j i).symm
      | inr j => exact Q.disjoint i j (fun h => hpq (congrArg Sum.inr h))

theorem sixExtension_bound (n m : ℕ) (hn : 7 ≤ n)
    (Q : PackingFamily (cyclePower n 6) (Fin m))
    (hc : ∀ p i, Disjoint (triangleEdges (sixTriangle n hn p)) (triangleEdges (Q.triangle i))) :
    (n - 3) / 2 + (n - 5) / 2 + (n - 6) / 2 + 2 + m ≤ packingNumber (cyclePower n 6) := by
  have h := (combinePacking
    ((sixPathPacking n hn).in_supergraph (pathPower_le_cyclePower n 6)) Q hc).number_bound
  simp only [Fintype.card_sum, SixIndex, SixPeriodicIndex, Fintype.card_sigma, Fintype.card_fin] at h
  simp [Fin.sum_univ_succ, sixAnchor, sixSpan] at h
  omega

end ResearchMain.PathCycleTuza
