import EdgeColoringMixing.TreeGeometry
import EdgeColoringMixing.MessageDomain

set_option autoImplicit false

/-! Exact branch factorization for every actual finite tree with forbidden vertex colors. -/
namespace EdgeColoringMixing.RootedCounting
open Finset TreeGeometry
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Proper edge colorings with the specified forbidden colors at every vertex. -/
abbrev Coloring (G : SimpleGraph V) (q : ℕ) (F : V → Finset (Fin q)) :=
  {σ : G.edgeSet → Fin q // Proper G q σ ∧
    ∀ e v, v ∈ e.1 → σ e ∉ F v}

noncomputable instance [Fintype V] (q : ℕ) (F : V → Finset (Fin q)) : Fintype (Coloring G q F) :=
  Fintype.ofFinite _
noncomputable instance [Fintype V] (r : V) : Fintype (G.neighborSet r) := Fintype.ofFinite _
noncomputable instance [Fintype V] (r : V) : DecidableEq (G.neighborSet r) := Classical.decEq _

/-- The original internal edges in one genuine child branch. -/
abbrev BranchEdge (hG : G.IsTree) (r : V) (i : G.neighborSet r) :=
  {e : InternalEdge G r // edgeBranch hG r e = i}

noncomputable instance [Fintype V] (hG : G.IsTree) (r : V) (i : G.neighborSet r) :
    Fintype (BranchEdge hG r i) := Fintype.ofFinite _

/-- A coloring of a branch without its parent edge. -/
abbrev BranchColoring (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) :=
  {σ : BranchEdge hG r i → Fin q //
    (∀ e f, G.lineGraph.Adj e.1.1 f.1.1 → σ e ≠ σ f) ∧
    ∀ e v, v ∈ e.1.1.1 → σ e ∉ F v}

noncomputable instance [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) :
    Fintype (BranchColoring hG r q F i) := Fintype.ofFinite _

/-- Compatibility with the parent's color checks exactly the child's incident edges. -/
def Compatible {hG : G.IsTree} {r : V} {q : ℕ} {F : V → Finset (Fin q)}
    {i : G.neighborSet r} (c : Fin q) (σ : BranchColoring hG r q F i) : Prop :=
  c ∉ F i.1 ∧ ∀ e, i.1 ∈ e.1.1.1 → σ.1 e ≠ c

/-- The two presentations of edges incident to the root are canonically equivalent. -/
noncomputable def incidentEquiv (r : V) :
    {e : G.edgeSet // r ∈ e.1} ≃ G.neighborSet r := by
  classical
  exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun e => e ∈ G.edgeSet) (fun e => r ∈ e)).trans
    (G.incidenceSetEquivNeighborSet r)

@[simp] theorem incidentEquiv_symm (r : V) (i : G.neighborSet r) :
    (incidentEquiv r).symm i = ⟨rootEdge r i, root_mem_rootEdge r i⟩ := rfl

/-- Every original edge is either a root edge or a unique internal branch edge. -/
noncomputable def edgeEquiv (hG : G.IsTree) (r : V) :
    G.edgeSet ≃ G.neighborSet r ⊕ ((i : G.neighborSet r) × BranchEdge hG r i) := by
  classical
  exact (Equiv.sumCompl (fun e : G.edgeSet => r ∈ e.1)).symm.trans
    (Equiv.sumCongr (incidentEquiv r) (Equiv.sigmaFiberEquiv (edgeBranch hG r)).symm)

@[simp] theorem edgeEquiv_symm_root (hG : G.IsTree) (r : V) (i : G.neighborSet r) :
    (edgeEquiv hG r).symm (.inl i) = rootEdge r i := rfl

@[simp] theorem edgeEquiv_symm_internal (hG : G.IsTree) (r : V)
    (i : G.neighborSet r) (e : BranchEdge hG r i) :
    (edgeEquiv hG r).symm (.inr ⟨i, e⟩) = e.1.1 := rfl

/-- Distinct actual root edges form a clique in the actual line graph. -/
theorem rootEdges_adj (r : V) (i j : G.neighborSet r) (hij : i ≠ j) :
    G.lineGraph.Adj (rootEdge r i) (rootEdge r j) := by
  exact SimpleGraph.lineGraph_adj_iff_exists.mpr
    ⟨fun h => hij (rootEdge_injective r h), r, root_mem_rootEdge r i, root_mem_rootEdge r j⟩

/-- The root colors form an actual injection, extracted from a proper full coloring. -/
noncomputable def rootInjection (_hG : G.IsTree) (r : V) {q : ℕ}
    {F : V → Finset (Fin q)} (σ : Coloring G q F) : G.neighborSet r ↪ Fin q where
  toFun i := σ.1 (rootEdge r i)
  inj' i j h := by
    by_contra hne
    exact σ.2.1 _ _ (rootEdges_adj r i j hne) h

/-- Restriction to a branch retains all original constraints. -/
def restrictBranch (hG : G.IsTree) (r : V) {q : ℕ} {F : V → Finset (Fin q)}
    (σ : Coloring G q F) (i : G.neighborSet r) : BranchColoring hG r q F i :=
  ⟨fun e => σ.1 e.1.1, ⟨fun e f h => σ.2.1 e.1.1 f.1.1 h, fun e v h => σ.2.2 e.1.1 v h⟩⟩

theorem restrictBranch_compatible (hG : G.IsTree) (r : V) {q : ℕ}
    {F : V → Finset (Fin q)} (σ : Coloring G q F) (i : G.neighborSet r) :
    Compatible (rootInjection hG r σ i) (restrictBranch hG r σ i) := by
  refine ⟨σ.2.2 _ i.1 (child_mem_rootEdge r i), ?_⟩
  intro e he
  exact σ.2.1 _ _ ((rootEdge_internal_adj_iff r i e.1).mpr he).symm

/-- Feasible root colors together with independent compatible branch colorings. -/
abbrev RootData (hG : G.IsTree) (r : V) (q : ℕ) (F : V → Finset (Fin q)) :=
  {D : (G.neighborSet r ↪ Fin q) × ((i : G.neighborSet r) → BranchColoring hG r q F i) //
    (∀ i, D.1 i ∉ F r) ∧ ∀ i, Compatible (D.1 i) (D.2 i)}

noncomputable instance [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ) (F : V → Finset (Fin q)) :
    Fintype (RootData hG r q F) := Fintype.ofFinite _

/-- Assemble actual edge colors from a choice of root colors and branch colorings. -/
noncomputable def assemble (hG : G.IsTree) (r : V) {q : ℕ} {F : V → Finset (Fin q)}
    (D : RootData hG r q F) (e : G.edgeSet) : Fin q :=
  match edgeEquiv hG r e with
  | .inl i => D.1.1 i
  | .inr ⟨i, f⟩ => (D.1.2 i).1 f

@[simp] theorem assemble_root (hG : G.IsTree) (r : V) {q : ℕ} {F : V → Finset (Fin q)}
    (D : RootData hG r q F) (i : G.neighborSet r) :
    assemble hG r D (rootEdge r i) = D.1.1 i := by
  have h := (edgeEquiv hG r).apply_symm_apply (.inl i)
  change edgeEquiv hG r (rootEdge r i) = _ at h
  simp [assemble, h]

@[simp] theorem assemble_internal (hG : G.IsTree) (r : V) {q : ℕ}
    {F : V → Finset (Fin q)} (D : RootData hG r q F)
    (i : G.neighborSet r) (e : BranchEdge hG r i) :
    assemble hG r D e.1.1 = (D.1.2 i).1 e := by
  have h := (edgeEquiv hG r).apply_symm_apply (.inr ⟨i, e⟩)
  change edgeEquiv hG r e.1.1 = _ at h
  simp [assemble, h]

/-- Assembly is proper on all pairs of original incident edges. -/
theorem assemble_proper (hG : G.IsTree) (r : V) {q : ℕ} {F : V → Finset (Fin q)}
    (D : RootData hG r q F) : Proper G q (assemble hG r D) := by
  intro e f hef
  obtain ⟨a, rfl⟩ := (edgeEquiv hG r).symm.surjective e
  obtain ⟨b, rfl⟩ := (edgeEquiv hG r).symm.surjective f
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simp only [edgeEquiv_symm_root, assemble_root]
      intro heq
      have hij := D.1.1.injective heq
      cases hij
      exact hef.ne rfl
    | inr b =>
      obtain ⟨j, f⟩ := b
      have h := edgeBranch_eq_of_rootEdge_adj hG r i f.1 hef
      have hij : i = j := h.symm.trans f.2
      cases hij
      simp only [edgeEquiv_symm_root, edgeEquiv_symm_internal, assemble_root, assemble_internal]
      exact ((D.2.2 i).2 f ((rootEdge_internal_adj_iff r i f.1).mp hef)).symm
  | inr a =>
    obtain ⟨i, e⟩ := a
    cases b with
    | inl j =>
      have h := edgeBranch_eq_of_rootEdge_adj hG r j e.1 hef.symm
      have hij : j = i := h.symm.trans e.2
      cases hij
      simp only [edgeEquiv_symm_root, edgeEquiv_symm_internal, assemble_root, assemble_internal]
      exact (D.2.2 i).2 e ((rootEdge_internal_adj_iff r i e.1).mp hef.symm)
    | inr b =>
      obtain ⟨j, f⟩ := b
      have h := edgeBranch_eq_of_adj hG r e.1 f.1 hef
      have hij : i = j := e.2.symm.trans (h.trans f.2)
      cases hij
      simp only [edgeEquiv_symm_internal, assemble_internal]
      exact (D.1.2 i).2.1 e f hef

/-- Assembly satisfies every original vertex's forbidden-color constraint. -/
theorem assemble_lists (hG : G.IsTree) (r : V) {q : ℕ} {F : V → Finset (Fin q)}
    (D : RootData hG r q F) (e : G.edgeSet) (v : V) (hv : v ∈ e.1) :
    assemble hG r D e ∉ F v := by
  obtain ⟨a, rfl⟩ := (edgeEquiv hG r).symm.surjective e
  cases a with
  | inl i =>
    simp only [edgeEquiv_symm_root, assemble_root]
    rcases Sym2.mem_iff.mp hv with h | h
    · subst v
      exact D.2.1 i
    · subst v
      exact (D.2.2 i).1
  | inr a =>
    obtain ⟨i, e⟩ := a
    simp only [edgeEquiv_symm_internal, assemble_internal]
    exact (D.1.2 i).2.2 e v hv

/-- Exact finite-tree factorization at an arbitrary root: the children form an
injection, and conditional on their colors every descendant branch is independent. -/
noncomputable def coloringEquivRootData (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) : Coloring G q F ≃ RootData hG r q F := by
  classical
  refine
    { toFun := fun σ => ⟨⟨rootInjection hG r σ, restrictBranch hG r σ⟩,
        ⟨fun i => σ.2.2 _ r (root_mem_rootEdge r i), fun i => restrictBranch_compatible hG r σ i⟩⟩
      invFun := fun D => ⟨assemble hG r D, assemble_proper hG r D, assemble_lists hG r D⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro σ
    apply Subtype.ext
    funext e
    obtain ⟨a, rfl⟩ := (edgeEquiv hG r).symm.surjective e
    cases a with
    | inl i => exact assemble_root hG r _ i
    | inr a =>
      obtain ⟨i, e⟩ := a
      exact assemble_internal hG r _ i e
  · intro D
    apply Subtype.ext
    apply Prod.ext
    · apply Function.Embedding.ext
      intro i
      exact assemble_root hG r D i
    · funext i
      apply Subtype.ext
      funext e
      exact assemble_internal hG r D i e

/-- Feasibility of the original coloring problem makes each branch coloring set nonempty. -/
theorem branch_nonempty (hG : G.IsTree) (r : V) (q : ℕ) (F : V → Finset (Fin q))
    (h : Nonempty (Coloring G q F)) (i : G.neighborSet r) :
    Nonempty (BranchColoring hG r q F i) := by
  obtain ⟨σ⟩ := h
  exact ⟨restrictBranch hG r σ i⟩

/-- The exact finite fibers over every possible injection of child colors. -/
noncomputable def rootDataEquivSigma (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) : RootData hG r q F ≃
    ((ρ : G.neighborSet r ↪ Fin q) × ((i : G.neighborSet r) →
      {σ : BranchColoring hG r q F i // ρ i ∉ F r ∧ Compatible (ρ i) σ})) where
  toFun D := ⟨D.1.1, fun i => ⟨D.1.2 i, D.2.1 i, D.2.2 i⟩⟩
  invFun D := ⟨⟨D.1, fun i => (D.2 i).1⟩,
    ⟨fun i => (D.2 i).2.1, fun i => (D.2 i).2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The cardinality factorization is over genuine finite-tree coloring sets. -/
theorem coloring_count [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) :
    Fintype.card (Coloring G q F) =
      ∑ ρ : G.neighborSet r ↪ Fin q, ∏ i : G.neighborSet r,
        Fintype.card {σ : BranchColoring hG r q F i // ρ i ∉ F r ∧ Compatible (ρ i) σ} := by
  classical
  rw [Fintype.card_congr ((coloringEquivRootData hG r q F).trans
    (rootDataEquivSigma hG r q F)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro ρ _
  exact Fintype.card_pi

/-- Child availability is a ratio of actual finite descendant-coloring counts. -/
noncomputable def childAvailability [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) (c : Fin q) : ℝ :=
  (Fintype.card {σ : BranchColoring hG r q F i // Compatible c σ} : ℝ) /
    Fintype.card (BranchColoring hG r q F i)

/-- The row weights are exactly the child's availability, masked by the root's pins. -/
noncomputable def rootWeight [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) (c : Fin q) : ℝ :=
  if c ∈ F r then 0 else childAvailability hG r q F i c

theorem rootWeight_eq_count [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) (c : Fin q) :
    rootWeight hG r q F i c =
      (Fintype.card {σ : BranchColoring hG r q F i // c ∉ F r ∧ Compatible c σ} : ℝ) /
        Fintype.card (BranchColoring hG r q F i) := by
  classical
  by_cases hc : c ∈ F r
  · have hempty : IsEmpty {σ : BranchColoring hG r q F i // c ∉ F r ∧ Compatible c σ} :=
      ⟨fun σ => σ.2.1 hc⟩
    let _ := hempty
    simp [rootWeight, hc]
  · simp [rootWeight, hc, childAvailability]

/-- The weighted injection partition function is the original number of colorings
divided by the product of the descendant normalizers. -/
theorem root_partition_eq [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) :
    (∑ ρ : G.neighborSet r ↪ Fin q, ∏ i, rootWeight hG r q F i (ρ i)) =
      (Fintype.card (Coloring G q F) : ℝ) /
        ∏ i : G.neighborSet r, (Fintype.card (BranchColoring hG r q F i) : ℝ) := by
  classical
  simp_rw [rootWeight_eq_count, Finset.prod_div_distrib]
  rw [← Finset.sum_div, coloring_count hG r q F]
  simp only [Nat.cast_sum, Nat.cast_prod]

/-- A finite sigma-type event depending only on its first coordinate. -/
theorem card_sigma_event {I : Type*} [Fintype I] (B : I → Type*) [∀ i, Fintype (B i)]
    (P : I → Prop) [DecidablePred P] :
    Fintype.card {x : (i : I) × B i // P x.1} =
      ∑ i : I, if P i then Fintype.card (B i) else 0 := by
  classical
  let e : {x : (i : I) × B i // P x.1} ≃ ((i : I) × {b : B i // P i}) :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩ }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P i <;> simp [h]

/-- Count the actual colorings in which the root does not see a specified color. -/
theorem root_avoid_count [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (c : Fin q) :
    Fintype.card {σ : Coloring G q F // ∀ i : G.neighborSet r, σ.1 (rootEdge r i) ≠ c} =
      ∑ ρ : G.neighborSet r ↪ Fin q, if c ∉ Set.range ρ then
        ∏ i : G.neighborSet r,
          Fintype.card {σ : BranchColoring hG r q F i // ρ i ∉ F r ∧ Compatible (ρ i) σ}
        else 0 := by
  classical
  let E := (coloringEquivRootData hG r q F).trans (rootDataEquivSigma hG r q F)
  have hevent : ∀ σ : Coloring G q F,
      (∀ i : G.neighborSet r, σ.1 (rootEdge r i) ≠ c) ↔ c ∉ Set.range (E σ).1 := by
    intro σ
    change (∀ i : G.neighborSet r, σ.1 (rootEdge r i) ≠ c) ↔
      c ∉ Set.range (rootInjection hG r σ)
    simp only [Set.mem_range, not_exists]
    rfl
  rw [Fintype.card_congr (E.subtypeEquiv (q := fun x => c ∉ Set.range x.1) hevent)]
  refine (card_sigma_event
    (fun ρ : G.neighborSet r ↪ Fin q => (i : G.neighborSet r) →
      {σ : BranchColoring hG r q F i // ρ i ∉ F r ∧ Compatible (ρ i) σ})
    (fun ρ => c ∉ Set.range ρ)).trans ?_
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases h : c ∈ Set.range ρ <;> simp [h, Fintype.card_pi]

/-- Renumbering any finite row set gives exactly the existing weighted-injection partition. -/
theorem partition_reindex_finite {I : Type*} [Fintype I] {d q : ℕ}
    (e : Fin d ≃ I) (W : I → Fin q → ℝ) :
    WeightedInjection.partition (fun i => W (e i)) =
      ∑ ρ : I ↪ Fin q, ∏ i : I, W i (ρ i) := by
  classical
  unfold WeightedInjection.partition WeightedInjection.weight
  apply Fintype.sum_equiv (e.embeddingCongr (Equiv.refl (Fin q)))
  intro σ
  apply Fintype.prod_equiv e
  intro i
  simp

/-- The original root message, defined from its actual finite coloring set. -/
noncomputable def rootAvailability [Fintype V] (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (c : Fin q) : ℝ :=
  if c ∈ F r then 0 else
    (Fintype.card {σ : Coloring G q F // ∀ i : G.neighborSet r, σ.1 (rootEdge r i) ≠ c} : ℝ) /
      Fintype.card (Coloring G q F)

/-- Renumbering also preserves the exact unused-color event numerator. -/
theorem partition_withoutColor_reindex_finite {I : Type*} [Fintype I] {d q : ℕ}
    (e : Fin d ≃ I) (W : I → Fin q → ℝ) (c : Fin q) :
    WeightedInjection.partition (WeightedInjection.withoutColor (fun i => W (e i)) c) =
      ∑ ρ : I ↪ Fin q, if c ∉ Set.range ρ then ∏ i : I, W i (ρ i) else 0 := by
  classical
  change WeightedInjection.partition (fun i b => if b = c then 0 else W (e i) b) = _
  rw [partition_reindex_finite e (fun i b => if b = c then 0 else W i b)]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hc : c ∈ Set.range ρ
  · simp only [hc, not_true_eq_false, ite_false]
    obtain ⟨i, hi⟩ := hc
    apply Finset.prod_eq_zero (mem_univ i)
    simp [hi]
  · simp only [hc, not_false_eq_true, ite_true]
    apply Finset.prod_congr rfl
    intro i _
    have hi : ρ i ≠ c := fun h => hc ⟨i, h⟩
    simp [hi]

/-- The deleted-color partition is also the ratio of the corresponding actual counts. -/
theorem root_unused_partition_eq [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (c : Fin q) :
    (∑ ρ : G.neighborSet r ↪ Fin q,
      if c ∉ Set.range ρ then ∏ i, rootWeight hG r q F i (ρ i) else 0) =
      (Fintype.card {σ : Coloring G q F // ∀ i : G.neighborSet r, σ.1 (rootEdge r i) ≠ c} : ℝ) /
        ∏ i : G.neighborSet r, (Fintype.card (BranchColoring hG r q F i) : ℝ) := by
  classical
  simp_rw [rootWeight_eq_count, Finset.prod_div_distrib]
  rw [root_avoid_count hG r q F c, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hc : c ∈ Set.range ρ <;> simp [hc, Nat.cast_prod]

/-- Lemma 3.2's exact availability recursion for every actual finite tree.
The child messages are normalized counts on its uniquely determined genuine branches. -/
theorem rootAvailability_recursion [Fintype V] (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) {d : ℕ}
    (e : Fin d ≃ G.neighborSet r) (c : Fin q) :
    rootAvailability (G := G) r q F c =
      availabilityStep (F r) (fun i => childAvailability hG r q F (e i)) c := by
  classical
  let B : ℝ := ∏ i : G.neighborSet r, (Fintype.card (BranchColoring hG r q F i) : ℝ)
  have hB : 0 < B := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast Fintype.card_pos_iff.mpr (branch_nonempty hG r q F hfull i)
  have hZ : (0 : ℝ) < Fintype.card (Coloring G q F) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hfull
  have hW : maskedWeights (F r) (fun i => childAvailability hG r q F (e i)) =
      (fun i => rootWeight hG r q F (e i)) := rfl
  have hden : WeightedInjection.partition
      (maskedWeights (F r) (fun i => childAvailability hG r q F (e i))) =
      (Fintype.card (Coloring G q F) : ℝ) / B := by
    rw [hW, partition_reindex_finite e, root_partition_eq hG r q F]
  have hnum : WeightedInjection.partition (WeightedInjection.withoutColor
      (maskedWeights (F r) (fun i => childAvailability hG r q F (e i))) c) =
      (Fintype.card {σ : Coloring G q F // ∀ i : G.neighborSet r, σ.1 (rootEdge r i) ≠ c} : ℝ) / B := by
    rw [hW, partition_withoutColor_reindex_finite e, root_unused_partition_eq hG r q F c]
  by_cases hc : c ∈ F r
  · simp [rootAvailability, availabilityStep, hc]
  · simp only [rootAvailability, availabilityStep, hc, ite_false, hnum, hden]
    field_simp

end EdgeColoringMixing.RootedCounting
