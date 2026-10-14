import Fan.Components

namespace Fan

variable {n : ℕ}

theorem component_card_le (F : Set (Sym2 (Vertex n))) :
    Nat.card (SimpleGraph.fromEdgeSet F).ConnectedComponent ≤ Fintype.card (Vertex n) := by
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_le_card_of_surjective (SimpleGraph.fromEdgeSet F).connectedComponentMk
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v => exact ⟨v,rfl⟩

theorem graphicRank_strictMono : StrictMono (fun F : GraphicFlat n => graphicRank F.val) := by
  classical
  intro F H hFH
  have hsub : F.val ⊆ H.val := le_of_lt hFH
  have hproper : F.val ≠ H.val := fun he => (ne_of_lt hFH) (Subtype.ext he)
  obtain ⟨e,heH,heF⟩ := Set.exists_of_ssubset (Set.ssubset_iff_subset_ne.mpr ⟨hsub,hproper⟩)
  have hre : ∃ v w, e=s(v,w) := by
    induction e using Sym2.inductionOn with
    | hf v w => exact ⟨v,w,rfl⟩
  obtain ⟨v,w,rfl⟩ := hre
  have hgraph : SimpleGraph.fromEdgeSet F.val ≤ SimpleGraph.fromEdgeSet H.val :=
    SimpleGraph.fromEdgeSet_mono hsub
  let f := SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hgraph)
  have hsur : Function.Surjective f := SimpleGraph.ConnectedComponent.surjective_map_ofLE hgraph
  have hnot : ¬Function.Injective f := by
    intro hinj
    have hreachH : (SimpleGraph.fromEdgeSet H.val).Reachable v w := by
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj H.val).mpr ⟨heH,(show (graph n).Adj v w from H.property.1 heH).ne⟩
    have heq := hinj (a₁:=(SimpleGraph.fromEdgeSet F.val).connectedComponentMk v)
      (a₂:=(SimpleGraph.fromEdgeSet F.val).connectedComponentMk w)
      (SimpleGraph.ConnectedComponent.sound hreachH)
    exact heF (F.property.2 v w (H.property.1 heH) (SimpleGraph.ConnectedComponent.exact heq))
  let : Fintype (SimpleGraph.fromEdgeSet F.val).ConnectedComponent := Fintype.ofFinite _
  let : Fintype (SimpleGraph.fromEdgeSet H.val).ConnectedComponent := Fintype.ofFinite _
  have hc := Fintype.card_lt_of_surjective_not_injective f hsur hnot
  simp only [← Nat.card_eq_fintype_card] at hc
  have hb := component_card_le F.val
  change Fintype.card (Vertex n)-Nat.card (SimpleGraph.fromEdgeSet F.val).ConnectedComponent < Fintype.card (Vertex n)-Nat.card (SimpleGraph.fromEdgeSet H.val).ConnectedComponent
  omega

theorem graphicRank_bottom (n : ℕ) : graphicRank (bottomFlat n).val=0 := by
  let G : SimpleGraph (Vertex n) := SimpleGraph.fromEdgeSet ∅
  have hinj : Function.Injective G.connectedComponentMk := by
    intro v w h
    have hr := SimpleGraph.ConnectedComponent.exact h
    simpa only [G,SimpleGraph.fromEdgeSet_empty,SimpleGraph.reachable_bot] using hr
  have hsur : Function.Surjective G.connectedComponentMk := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v,rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective G.connectedComponentMk ⟨hinj,hsur⟩)
  change Fintype.card (Vertex n)-Nat.card G.ConnectedComponent=0
  rw [← hc,Nat.card_eq_fintype_card,Nat.sub_self]

end Fan
