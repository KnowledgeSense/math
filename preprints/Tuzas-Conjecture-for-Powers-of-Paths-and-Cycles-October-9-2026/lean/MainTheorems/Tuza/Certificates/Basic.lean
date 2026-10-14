import MainTheorems.Tuza.CoChain
import MainTheorems.Tuza.Transfer
import Mathlib.Data.List.Chain

namespace ResearchMain.Tuza.Certificates

def vertices {V : Type*} [DecidableEq V] (t : V × V × V) : Finset V :=
  {t.1, t.2.1, t.2.2}

def edges {V : Type*} (t : V × V × V) : List (Sym2 V) :=
  [s(t.1, t.2.1), s(t.1, t.2.2), s(t.2.1, t.2.2)]

def edgeKey (n : ℕ) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun i j => min i.val j.val * n + max i.val j.val,
    by intro i j; simp [min_comm, max_comm]⟩

def distinctEdges {n : ℕ} (L : List (Fin n × Fin n × Fin n)) : Prop :=
  (((L.flatMap edges).map (edgeKey n)).insertionSort (· ≤ ·)).IsChain (· < ·)

instance {n : ℕ} (L : List (Fin n × Fin n × Fin n)) : Decidable (distinctEdges L) := by
  unfold distinctEdges
  infer_instance

theorem distinctEdges_nodup {n : ℕ} {L : List (Fin n × Fin n × Fin n)}
    (h : distinctEdges L) : (L.flatMap edges).Nodup := by
  apply List.Nodup.of_map (edgeKey n)
  exact (List.perm_insertionSort (· ≤ ·) _).nodup_iff.mp h.pairwise.nodup

theorem triangleEdges_subset_list {V : Type*} [DecidableEq V] (t : V × V × V) :
    triangleEdges (vertices t) ⊆ (edges t).toFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨hx, hy, hxy⟩ := mem_triangleEdges.mp he
    simp only [vertices, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [edges, Sym2.eq_swap]

def family {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph W) (f : V ↪ W) (L : List (V × V × V))
    (hclique : ∀ t ∈ L, G.Adj (f t.1) (f t.2.1) ∧
      G.Adj (f t.1) (f t.2.2) ∧ G.Adj (f t.2.1) (f t.2.2))
    (hnodup : (L.flatMap edges).Nodup) : PackingFamily G (Fin L.length) where
  triangle i := (vertices (L.get i)).map f
  clique i := by
    obtain ⟨h₁, h₂, h₃⟩ := hclique (L.get i) (List.get_mem _ _)
    apply G.is3Clique_iff.mpr
    refine ⟨_, _, _, h₁, h₂, h₃, ?_⟩
    simp [vertices]
  disjoint i j hij := by
    rw [triangleEdges_map, triangleEdges_map]
    apply (Finset.disjoint_map _).mpr
    have hp := (List.nodup_flatMap.mp hnodup).2
    have hd : List.Disjoint (edges (L.get i)) (edges (L.get j)) := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hp.rel_get_of_lt h
      · exact (hp.rel_get_of_lt h).symm
    apply Disjoint.mono (triangleEdges_subset_list _) (triangleEdges_subset_list _)
    apply Finset.disjoint_left.mpr
    intro e he he'
    exact List.disjoint_left.mp hd (List.mem_toFinset.mp he) (List.mem_toFinset.mp he')

theorem family_carrier {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph W) (f : V ↪ W) (L : List (V × V × V))
    (hclique : ∀ t ∈ L, G.Adj (f t.1) (f t.2.1) ∧
      G.Adj (f t.1) (f t.2.2) ∧ G.Adj (f t.2.1) (f t.2.2))
    (hnodup : (L.flatMap edges).Nodup) :
    (family G f L hclique hnodup).carrier =
      L.toFinset.image (fun t => (vertices t).map f) := by
  ext s
  simp only [PackingFamily.carrier, Finset.mem_image, Finset.mem_univ, true_and,
    family, List.mem_toFinset]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨L.get i, List.get_mem _ _, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
    exact ⟨i, rfl⟩

def labeledPacking (a b : ℕ) (triangles : List (Fin (a + b) × Fin (a + b) × Fin (a + b))) :
    Finset (Finset (Fin a ⊕ Fin b)) :=
  triangles.toFinset.image (fun t =>
    {finSumFinEquiv.symm t.1, finSumFinEquiv.symm t.2.1, finSumFinEquiv.symm t.2.2})

def cliqueCheck {a b : ℕ} (d : FerrersProfile a b)
    (L : List (Fin (a + b) × Fin (a + b) × Fin (a + b))) : Bool :=
  L.all (fun t => decide (
    d.graph.Adj (finSumFinEquiv.symm t.1) (finSumFinEquiv.symm t.2.1) ∧
    d.graph.Adj (finSumFinEquiv.symm t.1) (finSumFinEquiv.symm t.2.2) ∧
    d.graph.Adj (finSumFinEquiv.symm t.2.1) (finSumFinEquiv.symm t.2.2)))

theorem labeledPacking_correct {a b : ℕ} (d : FerrersProfile a b)
    (L : List (Fin (a + b) × Fin (a + b) × Fin (a + b)))
    (hclique : cliqueCheck d L = true)
    (hnodup : distinctEdges L) :
    Packing d.graph (labeledPacking a b L) ∧ (labeledPacking a b L).card = L.length := by
  have hc : ∀ t ∈ L, d.graph.Adj (finSumFinEquiv.symm t.1) (finSumFinEquiv.symm t.2.1) ∧
      d.graph.Adj (finSumFinEquiv.symm t.1) (finSumFinEquiv.symm t.2.2) ∧
      d.graph.Adj (finSumFinEquiv.symm t.2.1) (finSumFinEquiv.symm t.2.2) := by
    simpa only [cliqueCheck, List.all_eq_true, decide_eq_true_eq] using hclique
  let P := family d.graph finSumFinEquiv.symm.toEmbedding L hc (distinctEdges_nodup hnodup)
  have heq : P.carrier = labeledPacking a b L := by
    rw [family_carrier]
    simp [labeledPacking, vertices]
  rw [← heq]
  exact ⟨P.packing, by simpa using P.card⟩

end ResearchMain.Tuza.Certificates
