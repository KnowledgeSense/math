import HardCoreActivityThreshold.WeightedPartition

/-! Weighted forest partition recursions are proved for their actual finite graphs. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

section Transport
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem independent_map_iff (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (he : ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v)) (s : Finset V) :
    Independent H (s.map f) ↔ Independent G s := by
  constructor
  · intro h u hu v hv huv
    exact h (f u) (mem_map.mpr ⟨u, hu, rfl⟩) (f v) (mem_map.mpr ⟨v, hv, rfl⟩) ((he u v).mp huv)
  · intro h u hu v hv huv
    obtain ⟨u, hus, rfl⟩ := mem_map.mp hu
    obtain ⟨v, hvs, rfl⟩ := mem_map.mp hv
    exact h u hus v hvs ((he u v).mpr huv)

omit [DecidableEq V] [DecidableEq W] in
theorem partitionWithin_map (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (he : ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v)) (activity : W → ℝ) (s : Finset V) :
    partitionWithin H activity (s.map f) = partitionWithin G (fun v => activity (f v)) s := by
  unfold partitionWithin
  symm
  apply sum_bij (fun t _ => t.map f)
  · intro t ht
    rcases (Forest.mem_independentSetsWithin G).mp ht with ⟨hsub, hi⟩
    apply (Forest.mem_independentSetsWithin H).mpr
    exact ⟨map_subset_map.mpr hsub, (independent_map_iff G H f he t).mpr hi⟩
  · intro t ht u hu h
    exact map_injective f h
  · intro t ht
    rcases (Forest.mem_independentSetsWithin H).mp ht with ⟨hsub, hi⟩
    obtain ⟨u, hu, rfl⟩ := subset_map_iff.mp hsub
    exact ⟨u, (Forest.mem_independentSetsWithin G).mpr ⟨hu,
      (independent_map_iff G H f he u).mp hi⟩, rfl⟩
  · intro t _
    exact (prod_map t f activity).symm

end Transport

noncomputable def weightedTotal (A : ForestExpr) (activity : A.Vertex → ℝ) : ℝ :=
  partitionWithin A.graph activity univ

noncomputable def weightedAvoidRoots (A : ForestExpr) (activity : A.Vertex → ℝ) : ℝ :=
  partitionWithin A.graph activity (univ.filter (fun v => ¬ A.IsRoot v))

@[simp] theorem weightedTotal_empty (activity : ForestExpr.empty.Vertex → ℝ) :
    weightedTotal .empty activity = 1 := by
  simp [weightedTotal]

@[simp] theorem weightedAvoidRoots_empty (activity : ForestExpr.empty.Vertex → ℝ) :
    weightedAvoidRoots .empty activity = 1 := by
  simp [weightedAvoidRoots]

theorem weightedTotal_union (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ) :
    weightedTotal (A.union B) activity = weightedTotal A (fun v => activity (.inl v)) *
      weightedTotal B (fun v => activity (.inr v)) := by
  let f : A.Vertex ↪ (A.union B).Vertex := ⟨Sum.inl, Sum.inl_injective⟩
  let g : B.Vertex ↪ (A.union B).Vertex := ⟨Sum.inr, Sum.inr_injective⟩
  have he : (univ : Finset (A.union B).Vertex) = univ.map f ∪ univ.map g := by
    ext v
    cases v <;> simp [f, g]
  have hd : Disjoint (univ.map f) (univ.map g) := by
    rw [disjoint_left]
    intro v hv hw
    obtain ⟨u, _, hu⟩ := mem_map.mp hv
    obtain ⟨w, _, hw⟩ := mem_map.mp hw
    have h : Sum.inl u = Sum.inr w := hu.trans hw.symm
    cases h
  have hsep : Forest.Separated (A.union B).graph (univ.map f) (univ.map g) := by
    intro v hv w hw
    obtain ⟨v, _, rfl⟩ := mem_map.mp hv
    obtain ⟨w, _, rfl⟩ := mem_map.mp hw
    exact id
  unfold weightedTotal
  rw [he, partitionWithin_union _ _ hd hsep,
    partitionWithin_map A.graph (A.union B).graph f (fun _ _ => Iff.rfl),
    partitionWithin_map B.graph (A.union B).graph g (fun _ _ => Iff.rfl)]
  rfl

theorem weightedAvoidRoots_union (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ) :
    weightedAvoidRoots (A.union B) activity = weightedAvoidRoots A (fun v => activity (.inl v)) *
      weightedAvoidRoots B (fun v => activity (.inr v)) := by
  let f : A.Vertex ↪ (A.union B).Vertex := ⟨Sum.inl, Sum.inl_injective⟩
  let g : B.Vertex ↪ (A.union B).Vertex := ⟨Sum.inr, Sum.inr_injective⟩
  let sa := (univ : Finset A.Vertex).filter (fun v => ¬ A.IsRoot v)
  let sb := (univ : Finset B.Vertex).filter (fun v => ¬ B.IsRoot v)
  have he : (univ : Finset (A.union B).Vertex).filter (fun v => ¬ (A.union B).IsRoot v) =
      sa.map f ∪ sb.map g := by
    ext v
    cases v <;> simp [f, g, sa, sb, ForestExpr.IsRoot]
  have hd : Disjoint (sa.map f) (sb.map g) := by
    rw [disjoint_left]
    intro v hv hw
    obtain ⟨u, _, hu⟩ := mem_map.mp hv
    obtain ⟨w, _, hw⟩ := mem_map.mp hw
    have h : Sum.inl u = Sum.inr w := hu.trans hw.symm
    cases h
  have hsep : Forest.Separated (A.union B).graph (sa.map f) (sb.map g) := by
    intro v hv w hw
    obtain ⟨v, _, rfl⟩ := mem_map.mp hv
    obtain ⟨w, _, rfl⟩ := mem_map.mp hw
    exact id
  unfold weightedAvoidRoots
  rw [he, partitionWithin_union _ _ hd hsep,
    partitionWithin_map A.graph (A.union B).graph f (fun _ _ => Iff.rfl),
    partitionWithin_map B.graph (A.union B).graph g (fun _ _ => Iff.rfl)]
  rfl

theorem weightedRoot_deleted (A : ForestExpr) (activity : A.root.Vertex → ℝ) :
    partitionWithin A.root.graph activity (univ.erase none) = weightedTotal A (fun v => activity (some v)) := by
  let f : A.Vertex ↪ A.root.Vertex := ⟨Option.some, Option.some_injective A.Vertex⟩
  have he : (univ : Finset A.root.Vertex).erase none = univ.map f := by
    ext v
    cases v <;> simp [f]
  rw [he, partitionWithin_map A.graph A.root.graph f (fun _ _ => Iff.rfl)]
  rfl

theorem weightedRoot_compatible (A : ForestExpr) (activity : A.root.Vertex → ℝ) :
    partitionWithin A.root.graph activity (Forest.compatibleVertices A.root.graph univ none) =
      weightedAvoidRoots A (fun v => activity (some v)) := by
  let f : A.Vertex ↪ A.root.Vertex := ⟨Option.some, Option.some_injective A.Vertex⟩
  have he : Forest.compatibleVertices A.root.graph univ none =
      (univ.filter (fun v => ¬ A.IsRoot v)).map f := by
    ext v
    cases v <;> simp [Forest.mem_compatibleVertices, ForestExpr.graph, ForestExpr.Adj, f]
  rw [he, partitionWithin_map A.graph A.root.graph f (fun _ _ => Iff.rfl)]
  rfl

/-- Exact heterogeneous-activity root recursion. -/
theorem weightedTotal_root (A : ForestExpr) (activity : A.root.Vertex → ℝ) :
    weightedTotal A.root activity = weightedTotal A (fun v => activity (some v)) +
      activity none * weightedAvoidRoots A (fun v => activity (some v)) := by
  unfold weightedTotal
  rw [partitionWithin_recursion A.root.graph activity univ none (mem_univ none),
    weightedRoot_deleted, weightedRoot_compatible]
  rfl

theorem weightedAvoidRoots_root (A : ForestExpr) (activity : A.root.Vertex → ℝ) :
    weightedAvoidRoots A.root activity = weightedTotal A (fun v => activity (some v)) := by
  have he : (univ : Finset A.root.Vertex).filter (fun v => ¬ A.root.IsRoot v) = univ.erase none := by
    ext v
    cases v <;> simp [ForestExpr.IsRoot]
  unfold weightedAvoidRoots
  rw [he, weightedRoot_deleted]

/-- The exact heterogeneous root message is the odds of the actual hard-core law. -/
theorem weighted_root_odds (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    marginal (hardCoreLaw A.root.graph activity ha) none /
      (1-marginal (hardCoreLaw A.root.graph activity ha) none) =
      activity none * weightedAvoidRoots A (fun v => activity (some v)) /
        weightedTotal A (fun v => activity (some v)) := by
  rw [hardCore_occupation_odds, weightedRoot_compatible, weightedRoot_deleted]

end HardCoreActivityThreshold
