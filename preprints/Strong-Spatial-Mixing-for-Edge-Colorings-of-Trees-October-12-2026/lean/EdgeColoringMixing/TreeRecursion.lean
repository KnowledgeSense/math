import EdgeColoringMixing.TreeColorings
import EdgeColoringMixing.MessageDomain

set_option autoImplicit false

/-! Exact finite counting on the original graph edge set and the common pinned domain. -/
namespace EdgeColoringMixing.ActualColorings
open Finset

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) (q : ℕ)
    (Λ : Finset G.edgeSet) (τ : Λ → Fin q)

/-- Actual full proper extensions of the pinning. -/
abbrev Completion := {σ : G.edgeSet → Fin q // Proper G q σ ∧ Agrees Λ τ σ}

noncomputable instance : Fintype (Completion G q Λ τ) := by
  unfold Completion
  exact Fintype.ofFinite _

/-- Edges left after deleting precisely the common pinning domain. -/
abbrev FreeEdge := {e : G.edgeSet // e ∉ Λ}

noncomputable instance : Fintype (FreeEdge G Λ) := by
  unfold FreeEdge
  exact Fintype.ofFinite _
noncomputable instance : DecidableEq (FreeEdge G Λ) := Classical.decEq _

/-- Adjacency of the actual unpinned edges, without changing their identities. -/
def freeGraph : SimpleGraph (FreeEdge G Λ) := G.lineGraph.induce {e | e ∉ Λ}

/-- A free edge must avoid every pinned color at either of its endpoints. -/
def Allowed (e : FreeEdge G Λ) (c : Fin q) : Prop :=
  ∀ f : Λ, G.lineGraph.Adj e.1 f.1 → c ≠ τ f

/-- Proper colorings on the unpinned edges, including all constraints from the pins. -/
abbrev FreeColoring := {σ : FreeEdge G Λ → Fin q //
  (∀ e f, (freeGraph G Λ).Adj e f → σ e ≠ σ f) ∧
  ∀ e, Allowed G q Λ τ e (σ e)}

noncomputable instance : Fintype (FreeColoring G q Λ τ) := by
  unfold FreeColoring
  exact Fintype.ofFinite _

omit [Fintype V] in
/-- Feasibility supplies exactly the properness needed between two pinned edges. -/
theorem pinned_proper (hτ : Feasible G q Λ τ) (e f : Λ)
    (h : G.lineGraph.Adj e.1 f.1) : τ e ≠ τ f := by
  obtain ⟨σ, hσ, hagrees⟩ := hτ
  rw [← hagrees e, ← hagrees f]
  exact hσ e.1 f.1 h

/-- Restriction and extension give a bijection; no factor is discarded in the count. -/
noncomputable def completionEquivFree (hτ : Feasible G q Λ τ) :
    Completion G q Λ τ ≃ FreeColoring G q Λ τ := by
  classical
  refine
    { toFun := fun σ => ⟨fun e => σ.1 e.1, ?_⟩
      invFun := fun σ => ⟨fun e => if he : e ∈ Λ then τ ⟨e, he⟩ else σ.1 ⟨e, he⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro e f h
      exact σ.2.1 e.1 f.1 h
    · intro e f h
      rw [← σ.2.2 f]
      exact σ.2.1 e.1 f.1 h
  · constructor
    · intro e f h
      by_cases he : e ∈ Λ <;> by_cases hf : f ∈ Λ
      · simpa only [dite_eq_left he, dite_eq_left hf] using
          pinned_proper G q Λ τ hτ ⟨e, he⟩ ⟨f, hf⟩ h
      · simpa only [dite_eq_left he, dite_eq_right hf] using
          (σ.2.2 ⟨f, hf⟩ ⟨e, he⟩ h.symm).symm
      · simpa only [dite_eq_right he, dite_eq_left hf] using σ.2.2 ⟨e, he⟩ ⟨f, hf⟩ h
      · simpa only [dite_eq_right he, dite_eq_right hf] using σ.2.1 ⟨e, he⟩ ⟨f, hf⟩ h
    · intro f
      simp only [dite_eq_left f.2]
  · intro σ
    apply Subtype.ext
    funext e
    by_cases he : e ∈ Λ
    · simpa only [dite_eq_left he] using (σ.2.2 ⟨e, he⟩).symm
    · simp only [dite_eq_right he]
  · intro σ
    apply Subtype.ext
    funext e
    simp only [dite_eq_right e.2]

/-- The actual connected components of the unpinned line graph. -/
abbrev Component := (freeGraph G Λ).ConnectedComponent

noncomputable instance : Fintype (Component G Λ) := Fintype.ofFinite _
noncomputable instance : DecidableEq (Component G Λ) := Classical.decEq _

/-- The fiber consists of the original edges in one component. -/
abbrev Piece (K : Component G Λ) :=
  {e : FreeEdge G Λ // (freeGraph G Λ).connectedComponentMk e = K}

noncomputable instance (K : Component G Λ) : Fintype (Piece G Λ K) := by
  unfold Piece
  exact Fintype.ofFinite _

/-- A coloring of one genuine unpinned component with all its boundary constraints. -/
abbrev PieceColoring (K : Component G Λ) := {σ : Piece G Λ K → Fin q //
  (∀ e f, (freeGraph G Λ).Adj e.1 f.1 → σ e ≠ σ f) ∧
  ∀ e, Allowed G q Λ τ e.1 (σ e)}

noncomputable instance (K : Component G Λ) : Fintype (PieceColoring G q Λ τ K) := by
  unfold PieceColoring
  exact Fintype.ofFinite _

/-- No two distinct pieces interact, since an adjacency itself is a connecting path. -/
noncomputable def freeEquivPieces :
    FreeColoring G q Λ τ ≃ ((K : Component G Λ) → PieceColoring G q Λ τ K) := by
  classical
  refine
    { toFun := fun σ K => ⟨fun e => σ.1 e.1, ?_⟩
      invFun := fun σ => ⟨fun e => (σ ((freeGraph G Λ).connectedComponentMk e)).1 ⟨e, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ⟨fun e f h => σ.2.1 e.1 f.1 h, fun e => σ.2.2 e.1⟩
  · constructor
    · intro e f h
      have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h
      have hp := (σ ((freeGraph G Λ).connectedComponentMk e)).2.1
        ⟨e, rfl⟩ ⟨f, heq.symm⟩ h
      have eval_eq (K : Component G Λ) (f : FreeEdge G Λ)
          (hf : (freeGraph G Λ).connectedComponentMk f = K) :
          (σ ((freeGraph G Λ).connectedComponentMk f)).1 ⟨f, rfl⟩ =
            (σ K).1 ⟨f, hf⟩ := by
        subst K
        rfl
      intro hbad
      exact hp (hbad.trans (eval_eq _ f heq.symm))
    · intro e
      exact (σ ((freeGraph G Λ).connectedComponentMk e)).2.2 ⟨e, rfl⟩
  · intro σ
    rfl
  · intro σ
    funext K
    apply Subtype.ext
    funext e
    dsimp only
    rcases e with ⟨e, he⟩
    dsimp only
    subst K
    rfl

/-- Every actual completion is uniquely a choice of a coloring for each free component. -/
noncomputable def completionEquivPieces (hτ : Feasible G q Λ τ) :
    Completion G q Λ τ ≃ ((K : Component G Λ) → PieceColoring G q Λ τ K) :=
  (completionEquivFree G q Λ τ hτ).trans (freeEquivPieces G q Λ τ)

/-- The exact integer factorization of the full completion count. -/
theorem completion_count_factorization (hτ : Feasible G q Λ τ) :
    Fintype.card (Completion G q Λ τ) =
      ∏ K : Component G Λ, Fintype.card (PieceColoring G q Λ τ K) := by
  rw [Fintype.card_congr (completionEquivPieces G q Λ τ hτ), Fintype.card_pi]

omit [Fintype V] in
/-- Feasibility of the full pinning proves nonemptiness of every local coloring set. -/
theorem piece_nonempty (hτ : Feasible G q Λ τ) (K : Component G Λ) :
    Nonempty (PieceColoring G q Λ τ K) := by
  obtain ⟨σ, hσ⟩ := hτ
  exact ⟨completionEquivPieces G q Λ τ ⟨σ, hσ⟩ ⟨σ, hσ⟩ K⟩

/-- The completion subtype and the original finite completion set have identical size. -/
theorem completion_card : Fintype.card (Completion G q Λ τ) =
    (completions G q Λ τ).card := by
  classical
  unfold Completion completions
  exact Fintype.card_subtype _

/-- The original marginal is an exact ratio of actual completion counts. -/
theorem marginal_eq_completion_ratio (hτ : Feasible G q Λ τ) (e : G.edgeSet) (c : Fin q) :
    marginal G q Λ τ hτ e c =
      (Fintype.card {σ : Completion G q Λ τ // σ.1 e = c} : ℝ) /
        Fintype.card (Completion G q Λ τ) := by
  classical
  have hcard : Fintype.card {σ : Completion G q Λ τ // σ.1 e = c} =
      (univ.filter fun σ : G.edgeSet → Fin q =>
        (Proper G q σ ∧ Agrees Λ τ σ) ∧ σ e = c).card := by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun σ => Proper G q σ ∧ Agrees Λ τ σ) (fun σ => σ e = c))]
    exact Fintype.card_subtype _
  rw [hcard, completion_card]
  unfold marginal FiniteLaw.eventMass pinnedLaw
  have hpoint (σ : G.edgeSet → Fin q) :
      (if σ e = c then
        (if σ ∈ completions G q Λ τ then 1 / ((completions G q Λ τ).card : ℝ) else 0)
       else 0) =
      if (Proper G q σ ∧ Agrees Λ τ σ) ∧ σ e = c then
        1 / ((completions G q Λ τ).card : ℝ) else 0 := by
    by_cases he : σ e = c <;> by_cases hσ : Proper G q σ ∧ Agrees Λ τ σ <;>
      simp [he, hσ]
  simp only [hpoint, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Restriction to one actual free component is paired with completely independent
choices on the other components. -/
noncomputable def completionEquivOnePiece (hτ : Feasible G q Λ τ) (K : Component G Λ) :
    Completion G q Λ τ ≃ PieceColoring G q Λ τ K ×
      ((J : {J : Component G Λ // J ≠ K}) → PieceColoring G q Λ τ J.1) :=
  (completionEquivPieces G q Λ τ hτ).trans (Equiv.piSplitAt K _)

/-- Removing components outside the observed edge preserves the exact uniform marginal. -/
theorem marginal_eq_piece_ratio (hτ : Feasible G q Λ τ) (e : FreeEdge G Λ) (c : Fin q) :
    let K := (freeGraph G Λ).connectedComponentMk e
    marginal G q Λ τ hτ e.1 c =
      (Fintype.card {σ : PieceColoring G q Λ τ K // σ.1 ⟨e, rfl⟩ = c} : ℝ) /
        Fintype.card (PieceColoring G q Λ τ K) := by
  classical
  let K := (freeGraph G Λ).connectedComponentMk e
  let P := PieceColoring G q Λ τ K
  let R := (J : {J : Component G Λ // J ≠ K}) → PieceColoring G q Λ τ J.1
  let E := completionEquivOnePiece G q Λ τ hτ K
  have hE : ∀ σ : Completion G q Λ τ, σ.1 e.1 = c ↔ (E σ).1.1 ⟨e, rfl⟩ = c :=
    fun _ => Iff.rfl
  have hnum : Fintype.card {σ : Completion G q Λ τ // σ.1 e.1 = c} =
      Fintype.card {σ : P // σ.1 ⟨e, rfl⟩ = c} * Fintype.card R := by
    rw [Fintype.card_congr (E.subtypeEquiv (q := fun x => x.1.1 ⟨e, rfl⟩ = c) hE),
      Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun σ : P => σ.1 ⟨e, rfl⟩ = c) (β := R)), Fintype.card_prod]
  have hden : Fintype.card (Completion G q Λ τ) = Fintype.card P * Fintype.card R := by
    rw [Fintype.card_congr E, Fintype.card_prod]
  have hR : Nonempty R := by
    refine ⟨fun J => Classical.choice (piece_nonempty G q Λ τ hτ J.1)⟩
  have hRpos : (0 : ℝ) < Fintype.card R := by
    exact_mod_cast Fintype.card_pos_iff.mpr hR
  dsimp only
  rw [marginal_eq_completion_ratio, hnum, hden, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ hRpos.ne'

end EdgeColoringMixing.ActualColorings
