import EdgeColoringMixing.RootedInterpolation

set_option autoImplicit false

/-! Agreement above the cut is derived from the original common-domain line-graph distance. -/
namespace EdgeColoringMixing.RootedCounting
open TreeGeometry
universe u v w

/-- An actual rooted free subtree, placed in the original graph with its incoming edge. -/
structure RootPlacement {V : Type u} {O : Type v} (S : SimpleGraph V) (G : SimpleGraph O)
    (Λ : Finset G.edgeSet) (r : V) (p : G.edgeSet) where
  copy : SimpleGraph.Copy S G
  free_edges : ∀ e : S.edgeSet, copy.toLineGraphEmbedding e ∉ Λ
  incoming_free : p ∉ Λ
  root_incident : copy r ∈ p.1
  incoming_ne : ∀ e : S.edgeSet, p ≠ copy.toLineGraphEmbedding e

/-- The actual edge inclusions commute with composition of graph copies. -/
theorem copy_lineGraph_comp {V : Type u} {W : Type v} {O : Type w}
    {S : SimpleGraph V} {H : SimpleGraph W} {G : SimpleGraph O}
    (f : SimpleGraph.Copy H G) (g : SimpleGraph.Copy S H) (e : S.edgeSet) :
    (f.comp g).toLineGraphEmbedding e = f.toLineGraphEmbedding (g.toLineGraphEmbedding e) := by
  apply Subtype.ext
  change Sym2.map (fun x => f (g x)) e.1 = Sym2.map f (Sym2.map g e.1)
  rw [Sym2.map_map]
  rfl

namespace RootPlacement
variable {V : Type u} {O : Type v} {S : SimpleGraph V} {G : SimpleGraph O}
    {Λ : Finset G.edgeSet} {r : V} {p : G.edgeSet}

/-- The same placement invariant holds in every actual child tree. -/
def child (P : RootPlacement S G Λ r p) (i : S.neighborSet r) :
    RootPlacement (childGraph r i) G Λ (childRoot r i)
      (P.copy.toLineGraphEmbedding (rootEdge r i)) where
  copy := P.copy.comp (childEmbedding r i).toCopy
  free_edges e := by
    rw [copy_lineGraph_comp]
    exact P.free_edges _
  incoming_free := P.free_edges _
  root_incident := by
    exact Sym2.mem_map.mpr ⟨i.1, child_mem_rootEdge r i, rfl⟩
  incoming_ne e := by
    rw [copy_lineGraph_comp]
    intro h
    have he := P.copy.toLineGraphEmbedding.injective h
    have hr : r ∉ ((childEmbedding r i).toCopy.toLineGraphEmbedding e).1 := by
      intro hm
      obtain ⟨z, _, hz⟩ := Sym2.mem_map.mp hm
      exact z.1.2 hz
    exact hr ((congrArg (fun e : S.edgeSet => r ∈ e.1) he).mp (root_mem_rootEdge r i))

/-- Moving one level downward moves one step in the original line graph. -/
theorem incoming_child_adj (P : RootPlacement S G Λ r p) (i : S.neighborSet r) :
    G.lineGraph.Adj p (P.copy.toLineGraphEmbedding (rootEdge r i)) := by
  exact SimpleGraph.lineGraph_adj_iff_exists.mpr
    ⟨P.incoming_ne _, P.copy r, P.root_incident,
      Sym2.mem_map.mpr ⟨r, root_mem_rootEdge r i, rfl⟩⟩

theorem child_distance_le (P : RootPlacement S G Λ r p) (i : S.neighborSet r)
    (e : G.edgeSet) (k : ℕ) (hk : G.lineGraph.edist e p ≤ k) :
    G.lineGraph.edist e (P.copy.toLineGraphEmbedding (rootEdge r i)) ≤ (k + 1 : ℕ) := by
  calc
    _ ≤ G.lineGraph.edist e p + G.lineGraph.edist p
        (P.copy.toLineGraphEmbedding (rootEdge r i)) := G.lineGraph.edist_triangle
    _ ≤ (k : ℕ∞) + 1 := add_le_add hk
      (SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (Or.inl (P.incoming_child_adj i)))
    _ = _ := by simp

/-- Every pinned edge incident to the current root is one further original line-graph step away. -/
theorem incident_pin_distance_le (P : RootPlacement S G Λ r p) (e : G.edgeSet)
    (k : ℕ) (hk : G.lineGraph.edist e p ≤ k) (f : Λ) (hf : P.copy r ∈ f.1.1) :
    G.lineGraph.edist e f.1 ≤ (k + 1 : ℕ) := by
  have hpf : p ≠ f.1 := fun h => P.incoming_free (h.symm ▸ f.2)
  have hadj : G.lineGraph.Adj p f.1 :=
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hpf, P.copy r, P.root_incident, hf⟩
  calc
    _ ≤ G.lineGraph.edist e p + G.lineGraph.edist p f.1 := G.lineGraph.edist_triangle
    _ ≤ (k : ℕ∞) + 1 := add_le_add hk
      (SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (Or.inl hadj))
    _ = _ := by simp

end RootPlacement

/-- A disagreement in the actual common pinning domain bounds its defining infimum. -/
theorem disagreementDistance_le_pin {O : Type v} (G : SimpleGraph O) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q) (e : G.edgeSet) (f : Λ)
    (hf : τ f ≠ τ' f) : disagreementDistance G Λ τ τ' e ≤ G.lineGraph.edist e f.1 := by
  unfold disagreementDistance
  exact iInf_le_of_le f (by simp [hf])

/-- The original global disagreement distance forces every forbidden-color set above
an arbitrary depth cut to agree. It includes pins outside the observed free component. -/
theorem agreeToDepth_of_distance {O : Type v} (G : SimpleGraph O) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q) (e : G.edgeSet) (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (S : SimpleGraph V) (r : V) (p : G.edgeSet)
      (P : RootPlacement S G Λ r p) (F F' : V → Finset (Fin q)),
      (∀ v, (∀ f : Λ, P.copy v ∈ f.1.1 → τ f = τ' f) → F v = F' v) →
      ∀ k : ℕ, G.lineGraph.edist e p ≤ k →
        (k + n : ℕ) < disagreementDistance G Λ τ τ' e → AgreeToDepth n S r q F F' := by
  induction n with
  | zero => intro V _ S r p P F F' hF k hk hkn; trivial
  | succ n ih =>
    intro V _ S r p P F F' hF k hk hkn
    constructor
    · apply hF r
      intro f hf
      by_contra hneq
      have hdist := disagreementDistance_le_pin G Λ τ τ' e f hneq
      have hup := P.incident_pin_distance_le e k hk f hf
      have hnat : (k + 1 : ℕ∞) ≤ (k + (n + 1) : ℕ) := by exact_mod_cast (by omega : k + 1 ≤ k + (n + 1))
      exact (not_lt_of_ge (hdist.trans (hup.trans hnat))) hkn
    · intro i
      apply ih (childGraph r i) (childRoot r i)
        (P.copy.toLineGraphEmbedding (rootEdge r i)) (P.child i)
        (fun v => F ((childEmbedding r i) v)) (fun v => F' ((childEmbedding r i) v))
      · intro v hv
        exact hF ((childEmbedding r i) v) hv
      · exact P.child_distance_le i e k hk
      · simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hkn

/-- The initial observed edge has distance zero, so depth n is valid whenever n<ℓ. -/
theorem agreeToDepth_of_rootPlacement {O : Type v} (G : SimpleGraph O) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q) (e : G.edgeSet) (n : ℕ)
    {V : Type u} [Fintype V] (S : SimpleGraph V) (r : V)
    (P : RootPlacement S G Λ r e) (F F' : V → Finset (Fin q))
    (hF : ∀ v, (∀ f : Λ, P.copy v ∈ f.1.1 → τ f = τ' f) → F v = F' v)
    (hn : (n : ℕ∞) < disagreementDistance G Λ τ τ' e) :
    AgreeToDepth n S r q F F' := by
  exact agreeToDepth_of_distance G Λ τ τ' e n S r e P F F' hF 0 (by simp) (by simpa using hn)

/-- A cut deeper than the whole actual finite tree produces a constant path.
This explicitly handles short branches and trees with no vertices at the cutoff. -/
theorem interpolate_constant_of_card_le (n : ℕ) :
    ∀ {V : Type u} [Fintype V] (S : SimpleGraph V) (r : V) (q : ℕ)
      (F F' : V → Finset (Fin q)), Fintype.card V ≤ n → ∀ θ θ' : ℝ,
      interpolate n S r q F F' θ = interpolate n S r q F F' θ' := by
  induction n with
  | zero =>
    intro V _ S r q F F' hcard θ θ'
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    omega
  | succ n ih =>
    intro V _ S r q F F' hcard θ θ'
    change availabilityStep (F r) _ = availabilityStep (F r) _
    congr 1
    funext j
    apply ih
    have hlt := child_card_lt r ((Fintype.equivFin (S.neighborSet r)).symm j)
    omega

/-- Infinite original disagreement distance gives exactly equal local counting messages,
even when disagreements exist in other disconnected or pinned-off components. -/
theorem rootAvailability_eq_of_distance_top {O : Type v} (G : SimpleGraph O) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q) (e : G.edgeSet)
    {V : Type u} [Fintype V] (S : SimpleGraph V) (hS : S.IsTree) (r : V)
    (P : RootPlacement S G Λ r e) (F F' : V → Finset (Fin q))
    (hF : ∀ v, (∀ f : Λ, P.copy v ∈ f.1.1 → τ f = τ' f) → F v = F' v)
    (hf : Nonempty (Coloring S q F)) (hf' : Nonempty (Coloring S q F'))
    (hdist : disagreementDistance G Λ τ τ' e = ⊤) :
    rootAvailability (G := S) r q F = rootAvailability (G := S) r q F' := by
  let n := Fintype.card V
  have hagree : AgreeToDepth n S r q F F' :=
    agreeToDepth_of_rootPlacement G Λ τ τ' e n S r P F F' hF (by simp [hdist])
  calc
    _ = interpolate n S r q F F' 0 := (interpolate_zero n S hS r q F F' hf).symm
    _ = interpolate n S r q F F' 1 := interpolate_constant_of_card_le n S r q F F' le_rfl 0 1
    _ = _ := interpolate_one n S hS r q F F' hf' hagree

end EdgeColoringMixing.RootedCounting
