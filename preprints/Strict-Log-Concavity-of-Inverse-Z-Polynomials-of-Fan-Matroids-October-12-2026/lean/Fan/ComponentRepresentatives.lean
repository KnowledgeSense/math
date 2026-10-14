import Fan.Configurations
import Fan.Components

namespace Fan
open scoped Classical

theorem cuts_nonempty {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    (cuts F i).Nonempty := by
  let z : Fin n := ⟨0,by have := i.isLt; omega⟩
  refine ⟨z,?_⟩
  simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨by dsimp [z]; omega,?_⟩
  intro h hh
  dsimp [z] at hh
  omega

noncomputable def runStart {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) : Fin n :=
  (cuts F i).max' (cuts_nonempty F i)

theorem runStart_mem {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    runStart F i ∈ cuts F i := Finset.max'_mem _ _

theorem runStart_le {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    (runStart F i).val ≤ i.val := by
  have h := runStart_mem F i
  simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and] at h
  exact h.1

theorem cuts_runStart {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    cuts F (runStart F i)=cuts F i := by
  apply Finset.Subset.antisymm (cuts_mono F (runStart_le F i))
  intro j hj
  have hle : j ≤ runStart F i := Finset.le_max' _ _ hj
  simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
  exact ⟨hle,hj.2⟩

theorem runStart_reachable {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    (SimpleGraph.fromEdgeSet F).Reachable (some (runStart F i)) (some i) :=
  reachable_of_cuts_card_eq F _ _ (runStart_le F i) (congrArg Finset.card (cuts_runStart F i))

noncomputable def starts {n : ℕ} (F : Set (Sym2 (Vertex n))) : Finset (Fin n) :=
  Finset.univ \ ((readPair F).1 ∪ (readPair F).2)

theorem mem_starts {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) :
    i∈starts F ↔ spoke i∉F ∧ ∀ h : Fin n, h.val+1=i.val → rim h i∉F := by
  classical
  simp [starts,readPair,not_exists,not_and]

theorem runStart_mem_starts {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) (i : Fin n) (hi : spoke i∉F) :
    runStart F i∈starts F := by
  rw [mem_starts]
  refine ⟨?_,?_⟩
  · intro hs
    apply hi
    exact hF.2 none (some i) trivial
      ((selected_spoke_reachable hs).trans (runStart_reachable F i))
  · have h := runStart_mem F i
    simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and] at h
    exact h.2

theorem runStart_eq_self {n : ℕ} {F : Set (Sym2 (Vertex n))} {i : Fin n}
    (hi : i∈starts F) : runStart F i=i := by
  apply Fin.ext
  apply Nat.le_antisymm (runStart_le F i)
  have himem : i∈cuts F i := by
    simp only [cuts,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨le_rfl,(mem_starts F i).mp hi |>.2⟩
  exact Finset.le_max' _ _ himem

theorem cuts_eq_of_card_eq {n : ℕ} (F : Set (Sym2 (Vertex n))) (i j : Fin n)
    (hc : (cuts F i).card=(cuts F j).card) : cuts F i=cuts F j := by
  rcases le_total i.val j.val with h | h
  · exact Finset.eq_of_subset_of_card_le (cuts_mono F h) hc.ge
  · exact (Finset.eq_of_subset_of_card_le (cuts_mono F h) hc.le).symm

noncomputable def startLabel {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) : Vertex n → Option {i : Fin n // i∈starts F}
  | none => none
  | some i => if hi : spoke i∈F then none else some ⟨runStart F i,runStart_mem_starts hF i hi⟩

def startRepresentative {n : ℕ} (F : Set (Sym2 (Vertex n))) :
    Option {i : Fin n // i∈starts F} → Vertex n
  | none => none
  | some i => some i.val

theorem startLabel_preserved {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) {v w : Vertex n}
    (hr : (SimpleGraph.fromEdgeSet F).Reachable v w) : startLabel hF v=startLabel hF w := by
  classical
  have he := reachable_preserves_label hF.1 hF.triangleClosed hr
  cases v with
  | none =>
    cases w with
    | none => rfl
    | some j =>
      by_cases hj : spoke j∈F
      · simp only [startLabel,dite_eq_left hj]
      · simp [componentLabel,hj] at he
  | some i =>
    cases w with
    | none =>
      by_cases hi : spoke i∈F
      · simp only [startLabel,dite_eq_left hi]
      · simp [componentLabel,hi] at he
    | some j =>
      by_cases hi : spoke i∈F <;> by_cases hj : spoke j∈F
      · simp only [startLabel,dite_eq_left hi,dite_eq_left hj]
      · simp [componentLabel,hi,hj] at he
      · simp [componentLabel,hi,hj] at he
      · have hc : (cuts F i).card=(cuts F j).card := by
          simpa only [componentLabel,hi,hj,ite_false,Option.some.injEq] using he
        have hs := cuts_eq_of_card_eq F i j hc
        simp only [startLabel,dite_eq_right hi,dite_eq_right hj,Option.some.injEq,Subtype.mk.injEq]
        unfold runStart
        congr 1

theorem startRepresentative_reachable {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) (v : Vertex n) :
    (SimpleGraph.fromEdgeSet F).Reachable (startRepresentative F (startLabel hF v)) v := by
  classical
  cases v with
  | none => exact SimpleGraph.Reachable.rfl
  | some i =>
    by_cases hi : spoke i∈F
    · simpa only [startLabel,dite_eq_left hi,startRepresentative] using selected_spoke_reachable hi
    · simpa only [startLabel,dite_eq_right hi,startRepresentative] using runStart_reachable F i

theorem startLabel_representative {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) (c : Option {i : Fin n // i∈starts F}) :
    startLabel hF (startRepresentative F c)=c := by
  classical
  cases c with
  | none => rfl
  | some i =>
    have hi := ((mem_starts F i.val).mp i.property).1
    simp only [startRepresentative,startLabel,dite_eq_right hi,Option.some.injEq]
    exact Subtype.ext (runStart_eq_self i.property)

noncomputable def componentEquiv {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) :
    (SimpleGraph.fromEdgeSet F).ConnectedComponent ≃ Option {i : Fin n // i∈starts F} where
  toFun := Quot.lift (startLabel hF) (fun _ _ hr => startLabel_preserved hF hr)
  invFun c := (SimpleGraph.fromEdgeSet F).connectedComponentMk (startRepresentative F c)
  left_inv c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact SimpleGraph.ConnectedComponent.sound (startRepresentative_reachable hF v)
  right_inv := startLabel_representative hF

/-- The exact graphic rank of a fan flat is the size of the union of its spoke
indices and its selected path-join endpoints. -/
theorem graphicRank_readPair {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : IsGraphicFlat (graph n) F) :
    graphicRank F=((readPair F).1 ∪ (readPair F).2).card := by
  classical
  have hc := Nat.card_congr (componentEquiv hF)
  simp only [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_coe] at hc
  unfold graphicRank
  rw [Nat.card_eq_fintype_card,hc]
  simp only [Vertex,Fintype.card_option,Fintype.card_fin]
  have hs := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ((readPair F).1 ∪ (readPair F).2))
  simp only [Finset.card_univ,Fintype.card_fin] at hs
  change n+1-((starts F).card+1)=_
  dsimp [starts]
  omega

end Fan
