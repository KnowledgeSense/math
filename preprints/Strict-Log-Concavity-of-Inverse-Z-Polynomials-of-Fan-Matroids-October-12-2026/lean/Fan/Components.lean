import Fan.FlatClassification

namespace Fan
open scoped Classical

theorem cuts_mono {n : ℕ} (F : Set (Sym2 (Vertex n))) {i j : Fin n}
    (hij : i.val ≤ j.val) : cuts F i ⊆ cuts F j := by
  intro k hk
  simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
  exact ⟨hk.1.trans hij,hk.2⟩

theorem reachable_of_cuts_card_eq {n : ℕ} (F : Set (Sym2 (Vertex n)))
    (i j : Fin n) (hij : i.val ≤ j.val) (hc : (cuts F i).card=(cuts F j).card) :
    (SimpleGraph.fromEdgeSet F).Reachable (some i) (some j) := by
  generalize hj : j.val = m
  induction m using Nat.strong_induction_on generalizing i j with
  | h m ih =>
    by_cases he : i=j
    · subst j
      exact SimpleGraph.Reachable.rfl
    have hlt : i.val < j.val := by
      have hne : i.val≠j.val := fun h => he (Fin.ext h)
      omega
    let k : Fin n := ⟨j.val-1,by omega⟩
    have hkj : k.val+1=j.val := by dsimp [k]; omega
    have hik : i.val ≤ k.val := by omega
    have hcik := Finset.card_le_card (cuts_mono F hik)
    have hckj := cuts_card_successor F k j hkj
    have hr : rim k j ∈ F := by
      by_contra hr
      simp only [hr,ite_false] at hckj
      omega
    have hck : (cuts F i).card=(cuts F k).card := by
      simp only [hr,ite_true,Nat.add_zero] at hckj
      omega
    exact (ih k.val (by omega) i k hik hck rfl).trans (selected_rim_reachable hkj hr)

theorem reachable_iff_label_eq {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hsub : F ⊆ (graph n).edgeSet) (hF : TriangleClosed F) (v w : Vertex n) :
    (SimpleGraph.fromEdgeSet F).Reachable v w ↔ componentLabel F v=componentLabel F w := by
  classical
  refine ⟨reachable_preserves_label hsub hF,?_⟩
  intro he
  cases v with
  | none =>
    cases w with
    | none => exact SimpleGraph.Reachable.rfl
    | some j =>
      apply selected_spoke_reachable
      by_contra hj
      simp [componentLabel,hj] at he
  | some i =>
    cases w with
    | none =>
      apply SimpleGraph.Reachable.symm
      apply selected_spoke_reachable
      by_contra hi
      simp [componentLabel,hi] at he
    | some j =>
      by_cases hi : spoke i ∈ F
      · have hj : spoke j ∈ F := by
          by_contra hj
          simp [componentLabel,hi,hj] at he
        exact (selected_spoke_reachable hi).symm.trans (selected_spoke_reachable hj)
      · have hj : spoke j ∉ F := by
          intro hj
          simp [componentLabel,hi,hj] at he
        have hc : (cuts F i).card=(cuts F j).card := by
          simpa only [componentLabel,hi,hj,ite_false,Option.some.injEq] using he
        rcases le_total i.val j.val with hij | hji
        · exact reachable_of_cuts_card_eq F i j hij hc
        · exact (reachable_of_cuts_card_eq F j i hji hc.symm).symm

theorem graph_preconnected (n : ℕ) : (graph n).Preconnected := by
  have hub : ∀ v : Vertex n, (graph n).Reachable none v := by
    intro v
    cases v with
    | none => exact SimpleGraph.Reachable.rfl
    | some i => exact SimpleGraph.Adj.reachable (show (graph n).Adj none (some i) from trivial)
  intro v w
  exact (hub v).symm.trans (hub w)

theorem graph_rank (n : ℕ) : graphicRank (graph n).edgeSet=n := by
  let : Subsingleton (graph n).ConnectedComponent :=
    (graph_preconnected n).subsingleton_connectedComponent
  unfold graphicRank
  rw [SimpleGraph.fromEdgeSet_edgeSet,Nat.card_unique]
  simp only [Vertex,Fintype.card_option,Fintype.card_fin,Nat.add_sub_cancel]

end Fan
