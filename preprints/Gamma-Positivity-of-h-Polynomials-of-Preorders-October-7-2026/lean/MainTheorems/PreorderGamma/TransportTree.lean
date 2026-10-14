import MainTheorems.PreorderGamma.TransportSupport

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

theorem transportSupportGraph_connected (p : NaturalTransport r d s) (a₀ : L)
    (hcuts : ∀ A : Finset L, ∀ B : Finset R, A.Nonempty →
      (∀ a ∈ A, ∀ b, b ∉ B → p.flow a b = 0) →
      (∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0) →
      A = Finset.univ ∧ B = Finset.univ) :
    (transportSupportGraph p).Connected := by
  classical
  let A : Finset L := Finset.univ.filter fun a =>
    (transportSupportGraph p).Reachable (Sum.inl a₀) (Sum.inl a)
  let B : Finset R := Finset.univ.filter fun b =>
    (transportSupportGraph p).Reachable (Sum.inl a₀) (Sum.inr b)
  have hA : A.Nonempty := ⟨a₀, by simp [A]⟩
  have hout : ∀ a ∈ A, ∀ b, b ∉ B → p.flow a b = 0 := by
    intro a ha b hb
    by_contra hz
    have hadj : (transportSupportGraph p).Adj (Sum.inl a) (Sum.inr b) :=
      Nat.pos_of_ne_zero hz
    have hreach := (Finset.mem_filter.mp ha).2.trans hadj.reachable
    exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hreach⟩)
  have hin : ∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0 := by
    intro b hb a ha
    by_contra hz
    have hadj : (transportSupportGraph p).Adj (Sum.inr b) (Sum.inl a) :=
      Nat.pos_of_ne_zero hz
    have hreach := (Finset.mem_filter.mp hb).2.trans hadj.reachable
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hreach⟩)
  obtain ⟨hAu, hBu⟩ := hcuts A B hA hout hin
  apply (transportSupportGraph p).connected_iff_exists_forall_reachable.mpr
  refine ⟨Sum.inl a₀, ?_⟩
  intro v
  cases v with
  | inl a =>
    have ha : a ∈ A := hAu.symm ▸ Finset.mem_univ a
    exact (Finset.mem_filter.mp ha).2
  | inr b =>
    have hb : b ∈ B := hBu.symm ▸ Finset.mem_univ b
    exact (Finset.mem_filter.mp hb).2

theorem minimum_transport_support_tree (p : NaturalTransport r d s) (a₀ : L)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q)
    (hcuts : ∀ A : Finset L, ∀ B : Finset R, A.Nonempty →
      (∀ a ∈ A, ∀ b, b ∉ B → p.flow a b = 0) →
      (∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0) →
      A = Finset.univ ∧ B = Finset.univ) :
    (transportSupportGraph p).IsTree where
  connected := transportSupportGraph_connected p a₀ hcuts
  isAcyclic := minimum_transport_support_acyclic p hp

noncomputable def transportBranchRows (p : NaturalTransport r d s) (a₀ : L) (b₀ : R) :
    Finset L := by
  classical
  exact Finset.univ.filter fun a =>
    ((transportSupportGraph p).deleteEdges {s(Sum.inl a₀, Sum.inr b₀)}).Reachable
      (Sum.inl a₀) (Sum.inl a)

noncomputable def transportBranchColumns (p : NaturalTransport r d s) (a₀ : L) (b₀ : R) :
    Finset R := by
  classical
  exact Finset.univ.filter fun b =>
    ((transportSupportGraph p).deleteEdges {s(Sum.inl a₀, Sum.inr b₀)}).Reachable
      (Sum.inl a₀) (Sum.inr b)

@[simp] theorem mem_transportBranchRows {p : NaturalTransport r d s}
    {a₀ a : L} {b₀ : R} : a ∈ transportBranchRows p a₀ b₀ ↔
    ((transportSupportGraph p).deleteEdges {s(Sum.inl a₀, Sum.inr b₀)}).Reachable
      (Sum.inl a₀) (Sum.inl a) := by
  classical
  simp [transportBranchRows]

@[simp] theorem mem_transportBranchColumns {p : NaturalTransport r d s}
    {a₀ : L} {b₀ b : R} : b ∈ transportBranchColumns p a₀ b₀ ↔
    ((transportSupportGraph p).deleteEdges {s(Sum.inl a₀, Sum.inr b₀)}).Reachable
      (Sum.inl a₀) (Sum.inr b) := by
  classical
  simp [transportBranchColumns]

theorem transportBranchRows_nonempty (p : NaturalTransport r d s) (a₀ : L) (b₀ : R) :
    (transportBranchRows p a₀ b₀).Nonempty := ⟨a₀, by simp⟩

theorem transportBranchColumns_not_boundary (p : NaturalTransport r d s)
    (hacyc : (transportSupportGraph p).IsAcyclic) (a₀ : L) (b₀ : R)
    (hflow : 0 < p.flow a₀ b₀) : b₀ ∉ transportBranchColumns p a₀ b₀ := by
  rw [mem_transportBranchColumns]
  apply SimpleGraph.isBridge_iff.mp
  exact (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hacyc) hflow

theorem transportBranch_outside_flow_zero (p : NaturalTransport r d s)
    (a₀ : L) (b₀ : R) (a : L) (ha : a ∈ transportBranchRows p a₀ b₀)
    (b : R) (hb : b ∉ transportBranchColumns p a₀ b₀)
    (hne : a ≠ a₀ ∨ b ≠ b₀) : p.flow a b = 0 := by
  classical
  by_contra hz
  have hadj : (transportSupportGraph p).Adj (Sum.inl a) (Sum.inr b) :=
    Nat.pos_of_ne_zero hz
  have hedge : s(Sum.inl a, Sum.inr b) ∉
      ({s(Sum.inl a₀, Sum.inr b₀)} : Set (Sym2 (L ⊕ R))) := by
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, or_false]
    exact fun h => hne.elim (fun ha => ha h.1) (fun hb => hb h.2)
  have hd : ((transportSupportGraph p).deleteEdges
      {s(Sum.inl a₀, Sum.inr b₀)}).Adj (Sum.inl a) (Sum.inr b) :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hedge⟩
  exact hb (mem_transportBranchColumns.mpr
    ((mem_transportBranchRows.mp ha).trans hd.reachable))

theorem transportBranch_incoming_flow_zero (p : NaturalTransport r d s)
    (hacyc : (transportSupportGraph p).IsAcyclic) (a₀ : L) (b₀ : R)
    (hflow : 0 < p.flow a₀ b₀) (b : R)
    (hb : b ∈ transportBranchColumns p a₀ b₀) (a : L)
    (ha : a ∉ transportBranchRows p a₀ b₀) : p.flow a b = 0 := by
  classical
  by_contra hz
  have hne : b ≠ b₀ := fun h =>
    transportBranchColumns_not_boundary p hacyc a₀ b₀ hflow (h ▸ hb)
  have hadj : (transportSupportGraph p).Adj (Sum.inr b) (Sum.inl a) :=
    Nat.pos_of_ne_zero hz
  have hedge : s(Sum.inr b, Sum.inl a) ∉
      ({s(Sum.inl a₀, Sum.inr b₀)} : Set (Sym2 (L ⊕ R))) := by
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, false_or]
    exact fun h => hne h.1
  have hd : ((transportSupportGraph p).deleteEdges
      {s(Sum.inl a₀, Sum.inr b₀)}).Adj (Sum.inr b) (Sum.inl a) :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hedge⟩
  exact ha (mem_transportBranchRows.mpr
    ((mem_transportBranchColumns.mp hb).trans hd.reachable))

theorem reachable_delete_other_edge_of_endpoint_unreachable {V : Type*}
    (G : SimpleGraph V) (a₁ a₂ b v : V)
    (hreach : (G.deleteEdges {s(a₂, b)}).Reachable a₂ v)
    (hnot : ¬(G.deleteEdges {s(a₂, b)}).Reachable a₂ b) :
    (G.deleteEdges {s(a₁, b)}).Reachable a₂ v := by
  classical
  obtain ⟨w⟩ := hreach
  refine ⟨w.transfer _ ?_⟩
  intro e he
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨?_, ?_⟩
  · exact SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _)
      (w.edges_subset_edgeSet he)
  · intro hmem
    have heq : e = s(a₁, b) := Set.mem_singleton_iff.mp hmem
    rw [heq] at he
    have hb := w.snd_mem_support_of_mem_edges he
    exact hnot (w.takeUntil b hb).reachable

theorem transportBranchRows_disjoint_same_column (p : NaturalTransport r d s)
    (hacyc : (transportSupportGraph p).IsAcyclic) (a₁ a₂ : L) (b : R)
    (hflow₁ : 0 < p.flow a₁ b) (hflow₂ : 0 < p.flow a₂ b) (hne : a₁ ≠ a₂) :
    Disjoint (transportBranchRows p a₁ b) (transportBranchRows p a₂ b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hc₁ hc₂
  have hreach₁ := mem_transportBranchRows.mp hc₁
  have hreach₂ := mem_transportBranchRows.mp hc₂
  have hnot₂ : ¬((transportSupportGraph p).deleteEdges
      {s(Sum.inl a₂, Sum.inr b)}).Reachable (Sum.inl a₂) (Sum.inr b) := by
    exact fun h => transportBranchColumns_not_boundary p hacyc a₂ b hflow₂
      (mem_transportBranchColumns.mpr h)
  have hother := reachable_delete_other_edge_of_endpoint_unreachable
    (transportSupportGraph p) (Sum.inl a₁) (Sum.inl a₂) (Sum.inr b) (Sum.inl c)
    hreach₂ hnot₂
  have hedge : s(Sum.inl a₂, Sum.inr b) ∉
      ({s(Sum.inl a₁, Sum.inr b)} : Set (Sym2 (L ⊕ R))) := by
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inl.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, or_false, and_true]
    exact Ne.symm hne
  have hadj : ((transportSupportGraph p).deleteEdges
      {s(Sum.inl a₁, Sum.inr b)}).Adj (Sum.inl a₂) (Sum.inr b) :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hflow₂, hedge⟩
  have hreach := (hreach₁.trans hother.symm).trans hadj.reachable
  exact transportBranchColumns_not_boundary p hacyc a₁ b hflow₁
    (mem_transportBranchColumns.mpr hreach)

theorem transport_column_parent_exists (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root : L) (b : R) :
    ∃ a : L, 0 < p.flow a b ∧ root ∈ transportBranchRows p a b := by
  classical
  obtain ⟨w, hw⟩ := (htree.connected.preconnected (Sum.inl root) (Sum.inr b)).exists_isPath
  have hnil : ¬w.Nil := w.not_nil_of_ne (by simp)
  have hlast := w.adj_penultimate hnil
  have htrail : (w.dropLast.concat hlast).IsTrail := by
    simpa only [SimpleGraph.Walk.concat_dropLast] using hw.isTrail
  have hnot : s(w.penultimate, Sum.inr b) ∉ w.dropLast.edges :=
    (SimpleGraph.Walk.isTrail_concat hlast).mp htrail |>.2
  have hprefix : ((transportSupportGraph p).deleteEdges
      {s(w.penultimate, Sum.inr b)}).Reachable (Sum.inl root) w.penultimate :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨w.dropLast, hnot⟩
  cases hpen : w.penultimate with
  | inl a =>
    rw [hpen] at hlast hprefix
    exact ⟨a, hlast, mem_transportBranchRows.mpr hprefix.symm⟩
  | inr b' =>
    rw [hpen] at hlast
    exact False.elim hlast

theorem transport_column_parent_unique (p : NaturalTransport r d s)
    (hacyc : (transportSupportGraph p).IsAcyclic) (root a₁ a₂ : L) (b : R)
    (hflow₁ : 0 < p.flow a₁ b) (hflow₂ : 0 < p.flow a₂ b)
    (hroot₁ : root ∈ transportBranchRows p a₁ b)
    (hroot₂ : root ∈ transportBranchRows p a₂ b) : a₁ = a₂ := by
  by_contra hne
  exact Finset.disjoint_left.mp
    (transportBranchRows_disjoint_same_column p hacyc a₁ a₂ b hflow₁ hflow₂ hne)
    hroot₁ hroot₂

theorem transport_row_parent_exists (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root a : L) (hne : root ≠ a) :
    ∃ b : R, 0 < p.flow a b ∧ root ∉ transportBranchRows p a b := by
  classical
  obtain ⟨w, hw⟩ := (htree.connected.preconnected (Sum.inl root) (Sum.inl a)).exists_isPath
  have hnil : ¬w.Nil := w.not_nil_of_ne (fun h => hne (Sum.inl.inj h))
  have hlast := w.adj_penultimate hnil
  have htrail : (w.dropLast.concat hlast).IsTrail := by
    simpa only [SimpleGraph.Walk.concat_dropLast] using hw.isTrail
  have hnot : s(w.penultimate, Sum.inl a) ∉ w.dropLast.edges :=
    (SimpleGraph.Walk.isTrail_concat hlast).mp htrail |>.2
  have hprefix : ((transportSupportGraph p).deleteEdges
      {s(w.penultimate, Sum.inl a)}).Reachable (Sum.inl root) w.penultimate :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨w.dropLast, hnot⟩
  cases hpen : w.penultimate with
  | inl a' =>
    rw [hpen] at hlast
    exact False.elim hlast
  | inr b =>
    rw [hpen] at hlast hprefix
    have hprefix' : ((transportSupportGraph p).deleteEdges
        {s(Sum.inl a, Sum.inr b)}).Reachable (Sum.inl root) (Sum.inr b) := by
      simpa only [Sym2.eq_swap] using hprefix
    refine ⟨b, hlast, ?_⟩
    intro hroot
    have hreach := (mem_transportBranchRows.mp hroot).trans hprefix'
    exact transportBranchColumns_not_boundary p htree.isAcyclic a b hlast
      (mem_transportBranchColumns.mpr hreach)

theorem transport_row_parent_unique (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root a : L) (b₁ b₂ : R)
    (hroot₁ : root ∉ transportBranchRows p a b₁)
    (hroot₂ : root ∉ transportBranchRows p a b₂) : b₁ = b₂ := by
  classical
  obtain ⟨w, hw⟩ := (htree.connected.preconnected (Sum.inl root) (Sum.inl a)).exists_isPath
  have hnot₁ : ¬((transportSupportGraph p).deleteEdges
      {s(Sum.inl a, Sum.inr b₁)}).Reachable (Sum.inl root) (Sum.inl a) :=
    fun h => hroot₁ (mem_transportBranchRows.mpr h.symm)
  have hnot₂ : ¬((transportSupportGraph p).deleteEdges
      {s(Sum.inl a, Sum.inr b₂)}).Reachable (Sum.inl root) (Sum.inl a) :=
    fun h => hroot₂ (mem_transportBranchRows.mpr h.symm)
  have he₁ := w.mem_edges_of_not_reachable_deleteEdges hnot₁
  have he₂ := w.mem_edges_of_not_reachable_deleteEdges hnot₂
  have hp₁ := hw.eq_penultimate_of_mem_edges he₁
  have hp₂ := hw.eq_penultimate_of_mem_edges he₂
  exact Sum.inr.inj (hp₁.trans hp₂.symm)

end ResearchMain.PreorderGamma
