import MainTheorems.PathCycleTuza.CyclicMaps
import MainTheorems.Tuza.PackingEdges
import MainTheorems.Tuza.Constructions

namespace ResearchMain.PathCycleTuza

open Tuza

def cyclicTriangle {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (p : Fin m × Fin n) : Finset (Fin n) :=
  {p.2, cyclicMiddle n k F hn p, cyclicLast n k F hn p}

theorem cyclicTriangle_edges {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (p : Fin m × Fin n) : triangleEdges (cyclicTriangle n k F hn p) =
      {cyclicFirstEdge n k F hn p.1 p.2, cyclicSpanEdge n k F hn p.1 p.2,
        cyclicSecondEdge n k F hn p.1 p.2} := by
  have h := cyclicRelations n k F hn p
  exact triangleEdges_triple h.1.ne h.2.1.ne h.2.2.ne

theorem cyclicTriangle_length_mem {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (p : Fin m × Fin n) (e : Sym2 (Fin n)) (he : e ∈ triangleEdges (cyclicTriangle n k F hn p)) :
    cyclicLength e ∈ ({F.first p.1, F.second p.1, F.span p.1} : Finset ℕ) := by
  rw [cyclicTriangle_edges] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;>
    simp [cyclicFirstEdge_length, cyclicSpanEdge_length, cyclicSecondEdge_length]

def cyclicPacking {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n) :
    PackingFamily (cyclePower n k) (Fin m × Fin n) where
  triangle := cyclicTriangle n k F hn
  clique p := by
    have h := cyclicRelations n k F hn p
    exact (cyclePower n k).is3Clique_iff.mpr ⟨_, _, _, h.1, h.2.1, h.2.2, rfl⟩
  disjoint p q hpq := by
    apply Finset.disjoint_left.mpr
    intro e hep heq
    by_cases hij : p.1 = q.1
    · rw [cyclicTriangle_edges] at hep heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hep heq
      obtain ⟨i, x⟩ := p
      obtain ⟨j, y⟩ := q
      change i = j at hij
      subst j
      have hp := F.positive i
      have ho := F.ordered i
      rcases hep with rfl | rfl | rfl <;> rcases heq with heq | heq | heq
      all_goals
        have hlen := congrArg cyclicLength heq
        simp only [cyclicFirstEdge_length, cyclicSpanEdge_length, cyclicSecondEdge_length,
          DifferenceFamily.span] at hlen
        first
          | exact hpq (Prod.ext rfl ((cyclicFirstEdge_injective n k F hn i) heq))
          | exact hpq (Prod.ext rfl ((cyclicSpanEdge_injective n k F hn i) heq))
          | exact hpq (Prod.ext rfl ((cyclicSecondEdge_injective n k F hn i) heq))
          | omega
    · exact Finset.disjoint_left.mp (F.disjoint p.1 q.1 hij)
        (cyclicTriangle_length_mem n k F hn p e hep) (cyclicTriangle_length_mem n k F hn q e heq)

theorem cyclicPacking_bound {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n) :
    m * n ≤ packingNumber (cyclePower n k) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using (cyclicPacking n k F hn).number_bound

theorem cyclePower_mono (n : ℕ) {k ℓ : ℕ} (hk : k ≤ ℓ) : cyclePower n k ≤ cyclePower n ℓ := by
  intro x y h
  exact ⟨h.1, h.2.elim (fun h => Or.inl (h.trans hk)) (fun h => Or.inr (h.trans hk))⟩

theorem skolem_cycle_bound (n k m : ℕ) (hm : 3 * m + hookFlag m ≤ k) (hn : 2 * k < n) :
    m * n ≤ packingNumber (cyclePower n k) := by
  obtain ⟨D⟩ := exists_skolem m
  have hp := cyclicPacking_bound n _ D.differenceFamily (by omega)
  exact hp.trans (packingNumber_mono (cyclePower_mono n hm))

end ResearchMain.PathCycleTuza
