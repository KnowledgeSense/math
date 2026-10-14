import MainTheorems.PathCycleTuza.CyclicEdges
import MainTheorems.PathCycleTuza.DifferenceFamily

namespace ResearchMain.PathCycleTuza

def cyclicMiddle {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n) (p : Fin m × Fin n) : Fin n :=
  cyclicAdd n p.2 (F.first p.1) (by have hb := F.bounded p.1; omega)

def cyclicLast {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n) (p : Fin m × Fin n) : Fin n :=
  cyclicAdd n p.2 (F.span p.1) (by have hb : F.span p.1 ≤ k := F.bounded p.1; omega)

theorem cyclicLast_composed {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : cyclicLast n k F hn (i, x) =
      cyclicAdd n (cyclicMiddle n k F hn (i, x)) (F.second i) (by have hb := F.bounded i; omega) := by
  have hb := F.bounded i
  exact (cyclicAdd_compose n x (F.first i) (F.second i) (by omega)).symm

theorem cyclicRelations {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (p : Fin m × Fin n) :
    (cyclePower n k).Adj p.2 (cyclicMiddle n k F hn p) ∧
      (cyclePower n k).Adj p.2 (cyclicLast n k F hn p) ∧
      (cyclePower n k).Adj (cyclicMiddle n k F hn p) (cyclicLast n k F hn p) := by
  have hp := F.positive p.1
  have ho := F.ordered p.1
  have hb := F.bounded p.1
  refine ⟨cyclicAdd_adj n k (F.first p.1) p.2 hp (by omega) hn,
    cyclicAdd_adj n k (F.span p.1) p.2 (by unfold DifferenceFamily.span; omega)
      (F.bounded p.1) hn, ?_⟩
  rw [cyclicLast_composed]
  exact cyclicAdd_adj n k (F.second p.1) _ (by omega) (by omega) hn

def cyclicFirstEdge {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : Sym2 (Fin n) := s(x, cyclicMiddle n k F hn (i, x))

def cyclicSpanEdge {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : Sym2 (Fin n) := s(x, cyclicLast n k F hn (i, x))

def cyclicSecondEdge {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : Sym2 (Fin n) := s(cyclicMiddle n k F hn (i, x), cyclicLast n k F hn (i, x))

theorem cyclicFirstEdge_length {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : cyclicLength (cyclicFirstEdge n k F hn i x) = F.first i := by
  have hb := F.bounded i
  exact cyclicEdge_length n (F.first i) (by omega) (by omega) x

theorem cyclicSpanEdge_length {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : cyclicLength (cyclicSpanEdge n k F hn i x) = F.span i := by
  have hb : F.span i ≤ k := F.bounded i
  exact cyclicEdge_length n (F.span i) (by omega) (by omega) x

theorem cyclicSecondEdge_length {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) (x : Fin n) : cyclicLength (cyclicSecondEdge n k F hn i x) = F.second i := by
  have hb := F.bounded i
  unfold cyclicSecondEdge
  rw [cyclicLast_composed]
  exact cyclicEdge_length n (F.second i) (by omega) (by omega) _

theorem cyclicFirstEdge_injective {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) : Function.Injective (cyclicFirstEdge n k F hn i) := by
  have hb := F.bounded i
  exact cyclicEdge_injective n (F.first i) (by omega) (F.positive i) (by omega)

theorem cyclicSpanEdge_injective {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) : Function.Injective (cyclicSpanEdge n k F hn i) := by
  have hb : F.span i ≤ k := F.bounded i
  have hp : 0 < F.span i := by have := F.positive i; unfold DifferenceFamily.span; omega
  exact cyclicEdge_injective n (F.span i) (by omega) hp (by omega)

theorem cyclicSecondEdge_injective {m : ℕ} (n k : ℕ) (F : DifferenceFamily m k) (hn : 2 * k < n)
    (i : Fin m) : Function.Injective (cyclicSecondEdge n k F hn i) := by
  intro x y h
  have hb := F.bounded i
  have ho := F.ordered i
  have hp := F.positive i
  unfold cyclicSecondEdge at h
  simp only [cyclicLast_composed] at h
  have he := cyclicEdge_injective n (F.second i) (by omega) (by omega) (by omega) h
  exact cyclicAdd_injective n (F.first i) (by omega) he

end ResearchMain.PathCycleTuza
