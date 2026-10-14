import EdgeColoringMixing.CountedMessages

set_option autoImplicit false

/-! Depth-cut interpolation on actual finite trees, including branches ending above the cut. -/
namespace EdgeColoringMixing.RootedCounting
open Finset TreeGeometry
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The original vertex budget combines all forbidden colors and remaining incident edges. -/
def VertexBudget (Δ q : ℕ) (G : SimpleGraph V) (F : V → Finset (Fin q)) : Prop :=
  ∀ v, (F v).card + Fintype.card (G.neighborSet v) ≤ Δ

/-- A directed subtree root has one extra unit reserved for its absent parent edge. -/
def RootBudget (Δ q : ℕ) (G : SimpleGraph V) (r : V) (F : V → Finset (Fin q)) : Prop :=
  (F r).card + Fintype.card (G.neighborSet r) + 1 ≤ Δ

/-- A child-neighbor remains an actual original neighbor, injectively. -/
def childNeighborEmbedding (r : V) (i : G.neighborSet r) (v : childComponent r i) :
    (childGraph r i).neighborSet v ↪ G.neighborSet ((childEmbedding r i) v) where
  toFun w := ⟨(childEmbedding r i) w.1, w.2⟩
  inj' _ _ h := Subtype.ext ((childEmbedding r i).injective
    (congrArg (fun w : G.neighborSet ((childEmbedding r i) v) => w.1) h))

theorem child_neighbor_card_le (r : V) (i : G.neighborSet r) (v : childComponent r i) :
    Fintype.card ((childGraph r i).neighborSet v) ≤
      Fintype.card (G.neighborSet ((childEmbedding r i) v)) :=
  Fintype.card_le_of_injective _ (childNeighborEmbedding r i v).injective

/-- The child root has lost at least its original parent neighbor. -/
def childRootNeighborEmbedding (r : V) (i : G.neighborSet r) :
    (childGraph r i).neighborSet (childRoot r i) ↪
      {w : G.neighborSet i.1 // w.1 ≠ r} where
  toFun w := ⟨childNeighborEmbedding r i (childRoot r i) w, w.1.1.2⟩
  inj' _ _ h := (childNeighborEmbedding r i (childRoot r i)).injective
    (congrArg Subtype.val h)

theorem child_root_degree_lt (r : V) (i : G.neighborSet r) :
    Fintype.card ((childGraph r i).neighborSet (childRoot r i)) <
      Fintype.card (G.neighborSet i.1) := by
  classical
  apply (Fintype.card_le_of_injective _ (childRootNeighborEmbedding r i).injective).trans_lt
  exact Fintype.card_subtype_lt (x := (⟨r, i.2.symm⟩ : G.neighborSet i.1)) (by simp)

theorem VertexBudget.child {Δ q : ℕ} {F : V → Finset (Fin q)}
    (h : VertexBudget Δ q G F) (r : V) (i : G.neighborSet r) :
    VertexBudget Δ q (childGraph r i) (fun v => F ((childEmbedding r i) v)) := by
  intro v
  exact (Nat.add_le_add_left (child_neighbor_card_le r i v) _).trans
    (h ((childEmbedding r i) v))

theorem VertexBudget.child_root {Δ q : ℕ} {F : V → Finset (Fin q)}
    (h : VertexBudget Δ q G F) (r : V) (i : G.neighborSet r) :
    RootBudget Δ q (childGraph r i) (childRoot r i)
      (fun v => F ((childEmbedding r i) v)) := by
  have hdeg := child_root_degree_lt r i
  have hb := h i.1
  change (F i.1).card + Fintype.card ((childGraph r i).neighborSet (childRoot r i)) + 1 ≤ Δ
  omega

/-- Agreement is required only above the cut; childless branches impose no further condition. -/
def AgreeToDepth : (n : ℕ) → {V : Type u} → [Fintype V] → (G : SimpleGraph V) →
    (r : V) → (q : ℕ) → (F F' : V → Finset (Fin q)) → Prop
  | 0, _, _, _, _, _, _, _ => True
  | n + 1, _, _, G, r, q, F, F' => F r = F' r ∧ ∀ i : G.neighborSet r,
      AgreeToDepth n (childGraph r i) (childRoot r i) q
        (fun v => F ((childEmbedding r i) v)) (fun v => F' ((childEmbedding r i) v))

/-- At the cut we interpolate actual counting messages; above it we use exact recursion.
The definition remains valid when the cut is deeper than the tree. -/
noncomputable def interpolate : (n : ℕ) → {V : Type u} → [Fintype V] →
    (G : SimpleGraph V) → (r : V) → (q : ℕ) → (F F' : V → Finset (Fin q)) → ℝ → Fin q → ℝ
  | 0, _, _, G, r, q, F, F', θ => fun c =>
      (1 - θ) * rootAvailability (G := G) r q F c + θ * rootAvailability (G := G) r q F' c
  | n + 1, _, _, G, r, q, F, F', θ => availabilityStep (F r)
      (fun j : Fin (Fintype.card (G.neighborSet r)) =>
        let i := (Fintype.equivFin (G.neighborSet r)).symm j
        interpolate n (childGraph r i) (childRoot r i) q
          (fun v => F ((childEmbedding r i) v)) (fun v => F' ((childEmbedding r i) v)) θ)

/-- The left endpoint recovers the first exact coloring law at every cutoff depth. -/
theorem interpolate_zero (n : ℕ) : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
    (_hG : G.IsTree) (r : V) (q : ℕ) (F F' : V → Finset (Fin q)),
    Nonempty (Coloring G q F) → interpolate n G r q F F' 0 = rootAvailability (G := G) r q F := by
  induction n with
  | zero => intro V _ G hG r q F F' hfull; simp [interpolate]
  | succ n ih =>
    intro V _ G hG r q F F' hfull
    rw [rootAvailability_child_recursion hG r q F hfull]
    simp only [interpolate]
    congr 1
    funext j
    exact ih _ (childGraph_isTree hG r _) _ q _ _
      (child_coloring_nonempty hG r q F hfull _)

/-- Agreement above the cut makes the right endpoint the second exact coloring law. -/
theorem interpolate_one (n : ℕ) : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
    (_hG : G.IsTree) (r : V) (q : ℕ) (F F' : V → Finset (Fin q)),
    Nonempty (Coloring G q F') → AgreeToDepth n G r q F F' →
    interpolate n G r q F F' 1 = rootAvailability (G := G) r q F' := by
  induction n with
  | zero => intro V _ G hG r q F F' hfull hagree; simp [interpolate]
  | succ n ih =>
    intro V _ G hG r q F F' hfull hagree
    rw [rootAvailability_child_recursion hG r q F' hfull]
    change availabilityStep (F r) _ = availabilityStep (F' r) _
    rw [hagree.1]
    congr 1
    funext j
    exact ih _ (childGraph_isTree hG r _) _ q _ _
      (child_coloring_nonempty hG r q F' hfull _) (hagree.2 _)

/-- The entire finite-tree interpolation stays in H, including the arbitrary cut data. -/
theorem interpolate_mem_domain (n : ℕ) : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
    (_hG : G.IsTree) (r : V) (q Δ : ℕ) (F F' : V → Finset (Fin q)),
    Nonempty (Coloring G q F) → Nonempty (Coloring G q F') →
    VertexBudget Δ q G F → VertexBudget Δ q G F' →
    RootBudget Δ q G r F → RootBudget Δ q G r F' →
    0 < (q : ℝ) - 2 * Δ + 2 → ∀ θ ∈ Set.Icc (0 : ℝ) 1,
    MessageDomain Δ q (interpolate n G r q F F' θ) := by
  induction n with
  | zero =>
    intro V _ G hG r q Δ F F' hf hf' hb hb' hr hr' hs θ hθ
    exact (rootAvailability_mem_domain hG r q Δ F hf hr).convex_combination
      (rootAvailability_mem_domain hG r q Δ F' hf' hr') hθ.1 hθ.2
  | succ n ih =>
    intro V _ G hG r q Δ F F' hf hf' hb hb' hr hr' hs θ hθ
    apply availabilityStep_mem_domain
    · intro j
      exact ih _ (childGraph_isTree hG r _) _ q Δ _ _
        (child_coloring_nonempty hG r q F hf _) (child_coloring_nonempty hG r q F' hf' _)
        (hb.child r _) (hb'.child r _) (hb.child_root r _) (hb'.child_root r _) hs θ hθ
    · exact hr
    · exact hs

end EdgeColoringMixing.RootedCounting
