import EdgeColoringMixing.TreeRecursion
import EdgeColoringMixing.RootedCounting
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

/-! Exact transport of an actual common-domain pinning to forbidden vertex
colors on the graph with precisely the pinned edges deleted. -/
namespace EdgeColoringMixing.PinningForbidden
open Finset ActualColorings
universe u
variable {V : Type u} (G : SimpleGraph V) (q : ℕ)
    (Λ : Finset G.edgeSet) (τ : Λ → Fin q)

/-- The pinned edges as original unordered vertex pairs. -/
def pinnedEdges : Set (Sym2 V) := Set.range (fun f : Λ => f.1.1)

/-- The residual graph deletes exactly the common pinning domain. -/
def residualGraph : SimpleGraph V := G.deleteEdges (pinnedEdges G Λ)

/-- The forbidden colors at a vertex are exactly its incident pinned colors. -/
noncomputable def forbidden (v : V) : Finset (Fin q) := by
  classical
  exact (univ.filter (fun f : Λ => v ∈ f.1.1)).image τ

theorem mem_forbidden (v : V) (c : Fin q) :
    c ∈ forbidden G q Λ τ v ↔ ∃ f : Λ, v ∈ f.1.1 ∧ τ f = c := by
  classical
  simp [forbidden]

/-- The edge equivalence preserves the underlying original unordered edge. -/
noncomputable def residualEdgeEquiv : FreeEdge G Λ ≃ (residualGraph G Λ).edgeSet := by
  classical
  refine
    { toFun := fun e => ⟨e.1.1, ?_⟩
      invFun := fun e => ⟨⟨e.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [residualGraph, SimpleGraph.edgeSet_deleteEdges]
    refine ⟨e.1.2, ?_⟩
    rintro ⟨f, hf⟩
    have he : f.1 = e.1 := Subtype.ext hf
    exact e.2 (he ▸ f.2)
  · exact (show e.1 ∈ G.edgeSet ∧ e.1 ∉ pinnedEdges G Λ by
      simpa [residualGraph, SimpleGraph.edgeSet_deleteEdges] using e.2).1
  · intro he
    have hnot := (show e.1 ∈ G.edgeSet ∧ e.1 ∉ pinnedEdges G Λ by
      simpa [residualGraph, SimpleGraph.edgeSet_deleteEdges] using e.2).2
    exact hnot ⟨⟨⟨e.1, _⟩, he⟩, rfl⟩
  · intro e
    rfl
  · intro e
    rfl

@[simp] theorem residualEdgeEquiv_val (e : FreeEdge G Λ) :
    (residualEdgeEquiv G Λ e).1 = e.1.1 := rfl

@[simp] theorem residualEdgeEquiv_symm_val (e : (residualGraph G Λ).edgeSet) :
    ((residualEdgeEquiv G Λ).symm e).1.1 = e.1 := rfl

/-- Incidence and distinctness are preserved in the actual line graphs. -/
theorem residual_line_adj (e f : FreeEdge G Λ) :
    (residualGraph G Λ).lineGraph.Adj (residualEdgeEquiv G Λ e) (residualEdgeEquiv G Λ f) ↔
      (freeGraph G Λ).Adj e f := by
  change _ ↔ G.lineGraph.Adj e.1 f.1
  rw [SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, he, hf⟩
    refine ⟨?_, v, he, hf⟩
    intro hef
    exact hne (congrArg (residualEdgeEquiv G Λ) (Subtype.ext hef))
  · rintro ⟨hne, v, he, hf⟩
    refine ⟨?_, v, he, hf⟩
    intro hef
    exact hne (congrArg Subtype.val ((residualEdgeEquiv G Λ).injective hef))

/-- Avoiding adjacent pinned-edge colors is exactly avoiding the forbidden
sets at both endpoints of the same original free edge. -/
theorem allowed_iff_endpoint_forbidden (e : FreeEdge G Λ) (c : Fin q) :
    Allowed G q Λ τ e c ↔ ∀ v, v ∈ e.1.1 → c ∉ forbidden G q Λ τ v := by
  constructor
  · intro h v hv hc
    obtain ⟨f, hfv, hcolor⟩ := (mem_forbidden G q Λ τ v c).mp hc
    have hne : e.1 ≠ f.1 := fun he => e.2 (he ▸ f.2)
    exact h f (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, hv, hfv⟩) hcolor.symm
  · intro h f hef heq
    obtain ⟨_, v, he, hf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hef
    exact h v he ((mem_forbidden G q Λ τ v c).mpr ⟨f, hf, heq.symm⟩)

/-- Full coloring equivalence, preserving all original colors and constraints. -/
noncomputable def freeColoringEquivResidual :
    FreeColoring G q Λ τ ≃ RootedCounting.Coloring (residualGraph G Λ) q (forbidden G q Λ τ) := by
  classical
  let E := residualEdgeEquiv G Λ
  refine
    { toFun := fun σ => ⟨fun e => σ.1 (E.symm e), ?_⟩
      invFun := fun σ => ⟨fun e => σ.1 (E e), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro e f hef
      apply σ.2.1
      apply (residual_line_adj G Λ (E.symm e) (E.symm f)).mp
      simpa only [E, Equiv.apply_symm_apply] using hef
    · intro e v hv
      exact (allowed_iff_endpoint_forbidden G q Λ τ (E.symm e) _).mp (σ.2.2 (E.symm e)) v hv
  · constructor
    · intro e f hef
      exact σ.2.1 _ _ ((residual_line_adj G Λ e f).mpr hef)
    · intro e
      apply (allowed_iff_endpoint_forbidden G q Λ τ e _).mpr
      intro v hv
      exact σ.2.2 (E e) v hv
  · intro σ
    apply Subtype.ext
    funext e
    exact congrArg σ.1 (E.symm_apply_apply e)
  · intro σ
    apply Subtype.ext
    funext e
    exact congrArg σ.1 (E.apply_symm_apply e)

/-- The original full pinned-coloring problem and residual forbidden-color
problem have exactly the same configurations. -/
noncomputable def completionEquivResidual (hτ : Feasible G q Λ τ) :
    Completion G q Λ τ ≃ RootedCounting.Coloring (residualGraph G Λ) q (forbidden G q Λ τ) :=
  (completionEquivFree G q Λ τ hτ).trans (freeColoringEquivResidual G q Λ τ)

@[simp] theorem completionEquivResidual_apply (hτ : Feasible G q Λ τ)
    (σ : Completion G q Λ τ) (e : FreeEdge G Λ) :
    (completionEquivResidual G q Λ τ hτ σ).1 (residualEdgeEquiv G Λ e) = σ.1 e.1 := by
  simp [completionEquivResidual, freeColoringEquivResidual, completionEquivFree]

/-- Feasibility passes to the actual residual graph. -/
theorem residual_coloring_nonempty (hτ : Feasible G q Λ τ) :
    Nonempty (RootedCounting.Coloring (residualGraph G Λ) q (forbidden G q Λ τ)) := by
  obtain ⟨σ, hσ⟩ := hτ
  exact ⟨completionEquivResidual G q Λ τ ⟨σ, hσ⟩ ⟨σ, hσ⟩⟩

/-- Root-local equality of pins gives exact equality of the forbidden set there. -/
theorem forbidden_eq_of_incident_agreement (τ' : Λ → Fin q) (v : V)
    (h : ∀ f : Λ, v ∈ f.1.1 → τ f = τ' f) :
    forbidden G q Λ τ v = forbidden G q Λ τ' v := by
  ext c
  rw [mem_forbidden, mem_forbidden]
  constructor
  · rintro ⟨f, hf, hc⟩
    exact ⟨f, hf, (h f hf).symm.trans hc⟩
  · rintro ⟨f, hf, hc⟩
    exact ⟨f, hf, (h f hf).trans hc⟩

/-- Incident pins are still the original pinned edges, with multiplicity before
feasibility forces their colors to be distinct. -/
abbrev IncidentPinned (v : V) := {f : Λ // v ∈ f.1.1}

noncomputable instance (v : V) : Fintype (IncidentPinned G Λ v) := Fintype.ofFinite _

theorem forbidden_card_le (v : V) :
    (forbidden G q Λ τ v).card ≤ Fintype.card (IncidentPinned G Λ v) := by
  classical
  rw [forbidden, Fintype.card_subtype]
  exact Finset.card_image_le

/-- Feasibility makes the incident pin colors injective, exactly as properness requires. -/
theorem incident_pin_colors_injective (hτ : Feasible G q Λ τ) (v : V) :
    Function.Injective (fun f : IncidentPinned G Λ v => τ f.1) := by
  intro e f heq
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  exact pinned_proper G q Λ τ hτ e.1 f.1
    (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, e.2, f.2⟩) heq

theorem forbidden_card_eq (hτ : Feasible G q Λ τ) (v : V) :
    (forbidden G q Λ τ v).card = Fintype.card (IncidentPinned G Λ v) := by
  classical
  rw [forbidden, Fintype.card_subtype]
  apply Finset.card_image_of_injOn
  intro e he f hf heq
  have he' : v ∈ e.1.1 := by simpa using he
  have hf' : v ∈ f.1.1 := by simpa using hf
  exact congrArg Subtype.val (incident_pin_colors_injective G q Λ τ hτ v
    (show τ (⟨e, he'⟩ : IncidentPinned G Λ v).1 = τ (⟨f, hf'⟩ : IncidentPinned G Λ v).1 from heq))

/-- The original incident edges partition into residual incident edges and pins. -/
noncomputable def incidentPartitionEquiv (v : V) :
    {e : G.edgeSet // v ∈ e.1} ≃
      {e : (residualGraph G Λ).edgeSet // v ∈ e.1} ⊕ IncidentPinned G Λ v := by
  classical
  refine
    { toFun := fun e => if he : e.1 ∈ Λ then .inr ⟨⟨e.1, he⟩, e.2⟩
        else .inl ⟨residualEdgeEquiv G Λ ⟨e.1, he⟩, e.2⟩
      invFun := fun e => match e with
        | .inl e => ⟨((residualEdgeEquiv G Λ).symm e.1).1, e.2⟩
        | .inr e => ⟨e.1.1, e.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases he : e.1 ∈ Λ
    · simp only [dite_eq_left he]
    · simp only [dite_eq_right he]
      rfl
  · intro e
    cases e with
    | inl e =>
      have he : ((residualEdgeEquiv G Λ).symm e.1).1 ∉ Λ :=
        ((residualEdgeEquiv G Λ).symm e.1).2
      simp only [dite_eq_right he]
      congr 1
    | inr e =>
      simp only [dite_eq_left e.1.2]

/-- Exact residual-degree accounting on the original graph. -/
theorem residual_degree_add_incidentPins [Fintype V] (v : V) :
    Nat.card ((residualGraph G Λ).neighborSet v) + Fintype.card (IncidentPinned G Λ v) =
      Nat.card (G.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [← Fintype.card_congr (RootedCounting.incidentEquiv (G := residualGraph G Λ) v),
    ← Fintype.card_congr (RootedCounting.incidentEquiv (G := G) v)]
  exact (Fintype.card_congr (incidentPartitionEquiv G Λ v)).trans Fintype.card_sum |>.symm

/-- The degree budget needed by the exact availability domain, without assuming
that a proper pinning uses distinct colors unless that fact is needed. -/
theorem residual_degree_add_forbidden_le [Fintype V] (v : V) :
    Nat.card ((residualGraph G Λ).neighborSet v) + (forbidden G q Λ τ v).card ≤
      Nat.card (G.neighborSet v) := by
  rw [← residual_degree_add_incidentPins G Λ v]
  exact Nat.add_le_add_left (forbidden_card_le G q Λ τ v) _

theorem residual_degree_add_forbidden_eq [Fintype V] (hτ : Feasible G q Λ τ) (v : V) :
    Nat.card ((residualGraph G Λ).neighborSet v) + (forbidden G q Λ τ v).card =
      Nat.card (G.neighborSet v) := by
  rw [forbidden_card_eq G q Λ τ hτ v, residual_degree_add_incidentPins]

end EdgeColoringMixing.PinningForbidden

namespace EdgeColoringMixing.ComponentRestriction
open Finset
universe u
variable {V : Type u} (G : SimpleGraph V)

/-- The component containing either endpoint of an actual edge. -/
noncomputable def edgeComponent (e : G.edgeSet) : G.ConnectedComponent :=
  G.connectedComponentMk e.1.out.1

theorem edgeComponent_eq_of_mem (e : G.edgeSet) (v : V) (hv : v ∈ e.1) :
    edgeComponent G e = G.connectedComponentMk v := by
  by_cases heq : e.1.out.1 = v
  · exact congrArg G.connectedComponentMk heq
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (G.adj_iff_exists_edge.mpr ⟨heq, e.1, e.2, Sym2.out_fst_mem e.1, hv⟩)

theorem edgeComponent_eq_of_adj (e f : G.edgeSet) (hef : G.lineGraph.Adj e f) :
    edgeComponent G e = edgeComponent G f := by
  obtain ⟨_, v, he, hf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hef
  exact (edgeComponent_eq_of_mem G e v he).trans (edgeComponent_eq_of_mem G f v hf).symm

abbrev ComponentEdge (K : G.ConnectedComponent) := {e : G.edgeSet // edgeComponent G e = K}

noncomputable instance [Fintype V] (K : G.ConnectedComponent) : Fintype (ComponentEdge G K) :=
  Fintype.ofFinite _
noncomputable instance [Fintype V] : Fintype G.ConnectedComponent := Fintype.ofFinite _
noncomputable instance [Fintype V] (K : G.ConnectedComponent) : Fintype K := Fintype.ofFinite _

/-- Inclusion of the actual induced connected-component graph. -/
def componentEmbedding (K : G.ConnectedComponent) : K.toSimpleGraph ↪g G :=
  SimpleGraph.Embedding.induce K.supp

noncomputable def componentEdgeMap (K : G.ConnectedComponent)
    (e : K.toSimpleGraph.edgeSet) : ComponentEdge G K := by
  let e' := (componentEmbedding G K).toCopy.toLineGraphEmbedding e
  refine ⟨e', ?_⟩
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h v w =>
    exact (edgeComponent_eq_of_mem G e' v.1 (by
      change v.1 ∈ s(v.1, w.1)
      simp)).trans v.2

theorem componentEdgeMap_injective (K : G.ConnectedComponent) :
    Function.Injective (componentEdgeMap G K) := by
  intro e f hef
  exact (componentEmbedding G K).toCopy.toLineGraphEmbedding.injective
    (congrArg Subtype.val hef)

theorem componentEdgeMap_surjective (K : G.ConnectedComponent) :
    Function.Surjective (componentEdgeMap G K) := by
  intro e
  rcases e with ⟨⟨e, he⟩, hK⟩
  induction e using Sym2.ind with
  | h v w =>
    have hv : v ∈ K.supp :=
      (edgeComponent_eq_of_mem G ⟨s(v,w), he⟩ v (by simp)).symm.trans hK
    have hw : w ∈ K.supp :=
      (edgeComponent_eq_of_mem G ⟨s(v,w), he⟩ w (by simp)).symm.trans hK
    refine ⟨⟨s((⟨v,hv⟩ : K), (⟨w,hw⟩ : K)), he⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def componentEdgeEquiv (K : G.ConnectedComponent) :
    K.toSimpleGraph.edgeSet ≃ ComponentEdge G K :=
  Equiv.ofBijective _ ⟨componentEdgeMap_injective G K, componentEdgeMap_surjective G K⟩

/-- The original-edge presentation of a coloring of one component. -/
abbrev ComponentColoring (q : ℕ) (F : V → Finset (Fin q)) (K : G.ConnectedComponent) :=
  {σ : ComponentEdge G K → Fin q //
    (∀ e f, G.lineGraph.Adj e.1 f.1 → σ e ≠ σ f) ∧
      ∀ e v, v ∈ e.1.1 → σ e ∉ F v}

noncomputable instance [Fintype V] (q : ℕ) (F : V → Finset (Fin q)) (K : G.ConnectedComponent) :
    Fintype (ComponentColoring G q F K) := Fintype.ofFinite _

/-- The component's edge presentation transports to its actual induced graph. -/
noncomputable def componentColoringEquiv (q : ℕ) (F : V → Finset (Fin q))
    (K : G.ConnectedComponent) :
    ComponentColoring G q F K ≃ RootedCounting.Coloring K.toSimpleGraph q (fun v => F v.1) := by
  classical
  let E := componentEdgeEquiv G K
  let φ := (componentEmbedding G K).toCopy.toLineGraphEmbedding
  have hE (e : K.toSimpleGraph.edgeSet) : (E e).1 = φ e := rfl
  refine
    { toFun := fun σ => ⟨fun e => σ.1 (E e), ?_⟩
      invFun := fun σ => ⟨fun e => σ.1 (E.symm e), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro e f hef
      exact σ.2.1 (E e) (E f) (φ.map_rel_iff.mpr hef)
    · intro e v hv
      apply σ.2.2 (E e) v.1
      exact Sym2.mem_map.mpr ⟨v, hv, rfl⟩
  · constructor
    · intro e f hef
      apply σ.2.1
      apply φ.map_rel_iff.mp
      change G.lineGraph.Adj (E (E.symm e)).1 (E (E.symm f)).1
      simpa only [Equiv.apply_symm_apply] using hef
    · intro e v hv
      have hm : v ∈ ((E (E.symm e)).1).1 := by simpa using hv
      change v ∈ Sym2.map (componentEmbedding G K) (E.symm e).1 at hm
      obtain ⟨w, hw, hwv⟩ := Sym2.mem_map.mp hm
      have hw' := σ.2.2 (E.symm e) w hw
      have heq : w.1 = v := hwv
      simpa only [heq] using hw'
  · intro σ
    apply Subtype.ext
    funext e
    exact congrArg σ.1 (E.apply_symm_apply e)
  · intro σ
    apply Subtype.ext
    funext e
    exact congrArg σ.1 (E.symm_apply_apply e)

/-- Different connected components are genuinely independent coloring choices. -/
noncomputable def coloringEquivComponents (q : ℕ) (F : V → Finset (Fin q)) :
    RootedCounting.Coloring G q F ≃ ((K : G.ConnectedComponent) → ComponentColoring G q F K) := by
  classical
  refine
    { toFun := fun σ K => ⟨fun e => σ.1 e.1, ?_⟩
      invFun := fun σ => ⟨fun e => (σ (edgeComponent G e)).1 ⟨e, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ⟨fun e f h => σ.2.1 e.1 f.1 h, fun e v hv => σ.2.2 e.1 v hv⟩
  · constructor
    · intro e f hef
      have heq := edgeComponent_eq_of_adj G e f hef
      have hp := (σ (edgeComponent G e)).2.1 ⟨e,rfl⟩ ⟨f,heq.symm⟩ hef
      have eval_eq (K : G.ConnectedComponent) (f : G.edgeSet) (hf : edgeComponent G f = K) :
          (σ (edgeComponent G f)).1 ⟨f,rfl⟩ = (σ K).1 ⟨f,hf⟩ := by
        subst K
        rfl
      intro hbad
      exact hp (hbad.trans (eval_eq _ f heq.symm))
    · intro e v hv
      exact (σ (edgeComponent G e)).2.2 ⟨e,rfl⟩ v hv
  · intro σ
    rfl
  · intro σ
    funext K
    apply Subtype.ext
    funext e
    rcases e with ⟨e,he⟩
    dsimp only
    subst K
    rfl

/-- Restriction uses the actual induced connected-component graph, not an
unrelated local law or a fresh interpolation. -/
noncomputable def coloringEquivInducedComponents (q : ℕ) (F : V → Finset (Fin q)) :
    RootedCounting.Coloring G q F ≃
      ((K : G.ConnectedComponent) → RootedCounting.Coloring K.toSimpleGraph q (fun v => F v.1)) :=
  (coloringEquivComponents G q F).trans (Equiv.piCongrRight (componentColoringEquiv G q F))

@[simp] theorem coloringEquivInducedComponents_apply (q : ℕ) (F : V → Finset (Fin q))
    (σ : RootedCounting.Coloring G q F) (K : G.ConnectedComponent) (e : K.toSimpleGraph.edgeSet) :
    (coloringEquivInducedComponents G q F σ K).1 e = σ.1 (componentEdgeEquiv G K e).1 := rfl

/-- Feasibility gives nonempty coloring sets on every true component, including isolated vertices. -/
theorem component_coloring_nonempty (q : ℕ) (F : V → Finset (Fin q))
    (h : Nonempty (RootedCounting.Coloring G q F)) (K : G.ConnectedComponent) :
    Nonempty (RootedCounting.Coloring K.toSimpleGraph q (fun v => F v.1)) := by
  obtain ⟨σ⟩ := h
  exact ⟨coloringEquivInducedComponents G q F σ K⟩

/-- Canonical image of an original edge in its actual induced component. -/
noncomputable def edgeInComponent (e : G.edgeSet) : (edgeComponent G e).toSimpleGraph.edgeSet :=
  (componentEdgeEquiv G (edgeComponent G e)).symm ⟨e,rfl⟩

@[simp] theorem componentEdgeEquiv_edgeInComponent (e : G.edgeSet) :
    (componentEdgeEquiv G (edgeComponent G e) (edgeInComponent G e)).1 = e := by
  exact congrArg Subtype.val ((componentEdgeEquiv G (edgeComponent G e)).apply_symm_apply ⟨e,rfl⟩)

/-- Exact cancellation of all other components in a single-edge uniform marginal. -/
theorem coloring_marginal_eq_component [Fintype V] (q : ℕ) (F : V → Finset (Fin q))
    (h : Nonempty (RootedCounting.Coloring G q F)) (e : G.edgeSet) (c : Fin q) :
    (Fintype.card {σ : RootedCounting.Coloring G q F // σ.1 e = c} : ℝ) /
      Fintype.card (RootedCounting.Coloring G q F) =
    (Fintype.card {σ : RootedCounting.Coloring (edgeComponent G e).toSimpleGraph q
      (fun v => F v.1) // σ.1 (edgeInComponent G e) = c} : ℝ) /
      Fintype.card (RootedCounting.Coloring (edgeComponent G e).toSimpleGraph q (fun v => F v.1)) := by
  classical
  let K := edgeComponent G e
  let P := RootedCounting.Coloring K.toSimpleGraph q (fun v => F v.1)
  let R := (J : {J : G.ConnectedComponent // J ≠ K}) →
    RootedCounting.Coloring J.1.toSimpleGraph q (fun v => F v.1)
  let E := (coloringEquivInducedComponents G q F).trans (Equiv.piSplitAt K _)
  have hE : ∀ σ : RootedCounting.Coloring G q F,
      σ.1 e = c ↔ (E σ).1.1 (edgeInComponent G e) = c := by
    intro σ
    change σ.1 e = c ↔ (coloringEquivInducedComponents G q F σ K).1 (edgeInComponent G e) = c
    rw [coloringEquivInducedComponents_apply, componentEdgeEquiv_edgeInComponent]
  have hnum : Fintype.card {σ : RootedCounting.Coloring G q F // σ.1 e = c} =
      Fintype.card {σ : P // σ.1 (edgeInComponent G e) = c} * Fintype.card R := by
    rw [Fintype.card_congr (E.subtypeEquiv (q := fun x => x.1.1 (edgeInComponent G e) = c) hE),
      Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun σ : P => σ.1 (edgeInComponent G e) = c) (β := R)), Fintype.card_prod]
  have hden : Fintype.card (RootedCounting.Coloring G q F) = Fintype.card P * Fintype.card R := by
    rw [Fintype.card_congr E, Fintype.card_prod]
  have hR : Nonempty R := ⟨fun J => Classical.choice (component_coloring_nonempty G q F h J.1)⟩
  have hRpos : (0 : ℝ) < Fintype.card R := by
    exact_mod_cast Fintype.card_pos_iff.mpr hR
  rw [hnum, hden, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ hRpos.ne'

end EdgeColoringMixing.ComponentRestriction

namespace EdgeColoringMixing.PinningForbidden
open ActualColorings ComponentRestriction
universe u
variable {V : Type u} (G : SimpleGraph V) (q : ℕ)
    (Λ : Finset G.edgeSet) (τ : Λ → Fin q)

theorem residualGraph_le : residualGraph G Λ ≤ G := G.deleteEdges_le _

theorem residualGraph_isAcyclic (hG : G.IsAcyclic) : (residualGraph G Λ).IsAcyclic :=
  SimpleGraph.IsAcyclic.anti (residualGraph_le G Λ) hG

/-- The actual residual connected component containing the observed edge. -/
noncomputable def observedComponent (e : FreeEdge G Λ) : (residualGraph G Λ).ConnectedComponent :=
  edgeComponent (residualGraph G Λ) (residualEdgeEquiv G Λ e)

/-- The component is an actual finite induced tree after deleting the pins. -/
noncomputable def observedTree (e : FreeEdge G Λ) : SimpleGraph (observedComponent G Λ e) :=
  (observedComponent G Λ e).toSimpleGraph

/-- The original observed edge inside that actual induced tree. -/
noncomputable def observedEdge (e : FreeEdge G Λ) : (observedTree G Λ e).edgeSet :=
  edgeInComponent (residualGraph G Λ) (residualEdgeEquiv G Λ e)

theorem observedTree_isTree (hG : G.IsAcyclic) (e : FreeEdge G Λ) :
    (observedTree G Λ e).IsTree :=
  (residualGraph_isAcyclic G Λ hG).isTree_connectedComponent (observedComponent G Λ e)

theorem observedTree_coloring_nonempty (hτ : Feasible G q Λ τ) (e : FreeEdge G Λ) :
    Nonempty (RootedCounting.Coloring (observedTree G Λ e) q
      (fun v => forbidden G q Λ τ v.1)) :=
  component_coloring_nonempty (residualGraph G Λ) q (forbidden G q Λ τ)
    (residual_coloring_nonempty G q Λ τ hτ) (observedComponent G Λ e)

/-- First remove exactly the pinned edges, retaining the full counting measure. -/
theorem marginal_eq_residual_ratio [Fintype V] (hτ : Feasible G q Λ τ)
    (e : FreeEdge G Λ) (c : Fin q) :
    marginal G q Λ τ hτ e.1 c =
      (Fintype.card {σ : RootedCounting.Coloring (residualGraph G Λ) q (forbidden G q Λ τ) //
        σ.1 (residualEdgeEquiv G Λ e) = c} : ℝ) /
      Fintype.card (RootedCounting.Coloring (residualGraph G Λ) q (forbidden G q Λ τ)) := by
  classical
  rw [marginal_eq_completion_ratio]
  have heq : ∀ σ : Completion G q Λ τ,
      σ.1 e.1 = c ↔ (completionEquivResidual G q Λ τ hτ σ).1 (residualEdgeEquiv G Λ e) = c := by
    intro σ
    rw [completionEquivResidual_apply]
  rw [Fintype.card_congr ((completionEquivResidual G q Λ τ hτ).subtypeEquiv
    (q := fun σ => σ.1 (residualEdgeEquiv G Λ e) = c) heq),
    Fintype.card_congr (completionEquivResidual G q Λ τ hτ)]

/-- The original single-edge marginal is exactly the uniform forbidden-color
marginal in its actual residual induced tree; all other components cancel. -/
theorem marginal_eq_observedTree_ratio [Fintype V] (hτ : Feasible G q Λ τ)
    (e : FreeEdge G Λ) (c : Fin q) :
    marginal G q Λ τ hτ e.1 c =
      (Fintype.card {σ : RootedCounting.Coloring (observedTree G Λ e) q
        (fun v => forbidden G q Λ τ v.1) // σ.1 (observedEdge G Λ e) = c} : ℝ) /
      Fintype.card (RootedCounting.Coloring (observedTree G Λ e) q
        (fun v => forbidden G q Λ τ v.1)) := by
  rw [marginal_eq_residual_ratio]
  exact coloring_marginal_eq_component (residualGraph G Λ) q (forbidden G q Λ τ)
    (residual_coloring_nonempty G q Λ τ hτ) (residualEdgeEquiv G Λ e) c

/-- Every observed-component neighbor is a genuine residual neighbor. -/
def observedNeighborEmbedding (e : FreeEdge G Λ) (v : observedComponent G Λ e) :
    (observedTree G Λ e).neighborSet v ↪ (residualGraph G Λ).neighborSet v.1 where
  toFun w := ⟨w.1.1, w.2⟩
  inj' a b h := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : (residualGraph G Λ).neighborSet v.1 => w.1) h

/-- The original degree budget survives removal of pins and component restriction. -/
theorem observed_vertex_budget [Fintype V] {Δ : ℕ} (hΔ : DegreeBound G Δ)
    (e : FreeEdge G Λ) (v : observedComponent G Λ e) :
    (forbidden G q Λ τ v.1).card + Fintype.card ((observedTree G Λ e).neighborSet v) ≤ Δ := by
  have hc := Fintype.card_le_of_injective _ (observedNeighborEmbedding G Λ e v).injective
  have hd := residual_degree_add_forbidden_le G q Λ τ v.1
  rw [Nat.card_eq_fintype_card] at hd
  have ho := hΔ v.1
  omega

end EdgeColoringMixing.PinningForbidden

