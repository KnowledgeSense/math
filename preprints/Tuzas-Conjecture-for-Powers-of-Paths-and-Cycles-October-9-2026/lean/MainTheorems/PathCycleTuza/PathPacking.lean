import MainTheorems.PathCycleTuza.Basic
import MainTheorems.PathCycleTuza.DifferenceFamily
import MainTheorems.Tuza.PackingEdges
import MainTheorems.Tuza.Constructions

namespace ResearchMain.PathCycleTuza

open Tuza

def edgeLength {n : ℕ} : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => Nat.dist x.val y.val, by intro x y; exact Nat.dist_comm _ _⟩

def edgeStart {n : ℕ} : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun x y => min x.val y.val, by intro x y; exact min_comm _ _⟩

abbrev PathIndex {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) :=
  Σ i : Fin m, Fin (n - F.span i)

def pathTriple {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) (p : PathIndex n F) :
    Fin n × Fin n × Fin n :=
  let hx := p.2.isLt
  let hp := F.positive p.1
  let hs := F.ordered p.1
  (⟨p.2.val, by omega⟩,
    ⟨p.2.val + F.first p.1, by unfold DifferenceFamily.span at hx; omega⟩,
    ⟨p.2.val + F.span p.1, by omega⟩)

def pathTriangle {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) (p : PathIndex n F) :
    Finset (Fin n) :=
  let t := pathTriple n F p
  {t.1, t.2.1, t.2.2}

theorem pathTriple_ordered {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) (p : PathIndex n F) :
    (pathTriple n F p).1.val < (pathTriple n F p).2.1.val ∧
      (pathTriple n F p).2.1.val < (pathTriple n F p).2.2.val := by
  have hp := F.positive p.1
  have hs := F.ordered p.1
  dsimp [pathTriple, DifferenceFamily.span]
  omega

theorem path_triple_clique {n k : ℕ} (a b c : Fin n)
    (hab : a.val < b.val) (hbc : b.val < c.val) (hac : c.val - a.val ≤ k) :
    (pathPower n k).IsNClique 3 {a, b, c} := by
  apply (pathPower n k).is3Clique_iff.mpr
  refine ⟨a, b, c, ?_, ?_, ?_, rfl⟩
  all_goals
    refine ⟨?_, ?_⟩
    · intro he
      have h := congrArg Fin.val he
      omega
    · unfold Nat.dist
      omega

theorem pathTriangle_clique {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) (p : PathIndex n F) :
    (pathPower n k).IsNClique 3 (pathTriangle n F p) := by
  have ho := pathTriple_ordered n F p
  apply path_triple_clique _ _ _ ho.1 ho.2
  have hb := F.bounded p.1
  dsimp [pathTriple, DifferenceFamily.span]
  omega

theorem pathTriangle_edge_spec {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k)
    (p : PathIndex n F) (e : Sym2 (Fin n)) (he : e ∈ triangleEdges (pathTriangle n F p)) :
    (edgeLength e = F.first p.1 ∧ edgeStart e = p.2.val) ∨
      (edgeLength e = F.span p.1 ∧ edgeStart e = p.2.val) ∨
      (edgeLength e = F.second p.1 ∧ edgeStart e = p.2.val + F.first p.1) := by
  have ho := pathTriple_ordered n F p
  have hab : (pathTriple n F p).1 ≠ (pathTriple n F p).2.1 :=
    fun h => (ne_of_lt ho.1) (congrArg Fin.val h)
  have hac : (pathTriple n F p).1 ≠ (pathTriple n F p).2.2 :=
    fun h => (ne_of_lt (ho.1.trans ho.2)) (congrArg Fin.val h)
  have hbc : (pathTriple n F p).2.1 ≠ (pathTriple n F p).2.2 :=
    fun h => (ne_of_lt ho.2) (congrArg Fin.val h)
  change e ∈ triangleEdges {(pathTriple n F p).1, (pathTriple n F p).2.1,
    (pathTriple n F p).2.2} at he
  rw [triangleEdges_triple hab hac hbc] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  have hp := F.positive p.1
  have hs := F.ordered p.1
  rcases he with rfl | rfl | rfl
  all_goals
    simp only [edgeLength, edgeStart, Sym2.lift_mk]
    dsimp [pathTriple, DifferenceFamily.span]
    unfold Nat.dist
    omega

def pathPacking {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) :
    PackingFamily (pathPower n k) (PathIndex n F) where
  triangle := pathTriangle n F
  clique := pathTriangle_clique n F
  disjoint p q hpq := by
    apply Finset.disjoint_left.mpr
    intro e hep heq
    have hs₁ := pathTriangle_edge_spec n F p e hep
    have hs₂ := pathTriangle_edge_spec n F q e heq
    by_cases hij : p.1 = q.1
    · obtain ⟨i, x⟩ := p
      obtain ⟨j, y⟩ := q
      change i = j at hij
      subst j
      have hp := F.positive i
      have ho := F.ordered i
      have hxy : x.val = y.val := by
        dsimp only at hs₁ hs₂
        unfold DifferenceFamily.span at hs₁ hs₂
        rcases hs₁ with hs₁ | hs₁ | hs₁ <;> rcases hs₂ with hs₂ | hs₂ | hs₂ <;> omega
      exact hpq (congrArg (Sigma.mk i) (Fin.ext hxy))
    · have hl₁ : edgeLength e ∈ ({F.first p.1, F.second p.1, F.span p.1} : Finset ℕ) := by
        rcases hs₁ with h | h | h <;> simp [h.1]
      have hl₂ : edgeLength e ∈ ({F.first q.1, F.second q.1, F.span q.1} : Finset ℕ) := by
        rcases hs₂ with h | h | h <;> simp [h.1]
      exact Finset.disjoint_left.mp (F.disjoint p.1 q.1 hij) hl₁ hl₂

theorem pathPacking_bound {m k : ℕ} (n : ℕ) (F : DifferenceFamily m k) :
    (∑ i : Fin m, (n - F.span i)) ≤ packingNumber (pathPower n k) := by
  have h := (pathPacking n F).number_bound
  simpa only [PathIndex, Fintype.card_sigma, Fintype.card_fin] using h

end ResearchMain.PathCycleTuza
