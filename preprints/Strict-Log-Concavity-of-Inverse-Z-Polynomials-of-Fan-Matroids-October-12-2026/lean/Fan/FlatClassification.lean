import Fan.Definitions

namespace Fan
open scoped Classical

noncomputable def cuts {n : ℕ} (F : Set (Sym2 (Vertex n))) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => j.val ≤ i.val ∧
    ∀ h : Fin n, h.val+1=j.val → rim h j ∉ F

theorem cuts_successor {n : ℕ} (F : Set (Sym2 (Vertex n)))
    (i j : Fin n) (hij : i.val+1=j.val) :
    cuts F j = if rim i j ∈ F then cuts F i else insert j (cuts F i) := by
  classical
  have hpred (h : Fin n) (hh : h.val+1=j.val) : h=i := Fin.ext (by omega)
  ext k
  by_cases hr : rim i j ∈ F
  · simp only [hr, ite_true, cuts, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk,hcut⟩
      refine ⟨?_,hcut⟩
      by_contra hn
      have he : k=j := Fin.ext (by omega)
      subst k
      exact hcut i hij hr
    · rintro ⟨hk,hcut⟩
      exact ⟨by omega,hcut⟩
  · simp only [hr, ite_false, cuts, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hk,hcut⟩
      by_cases he : k=j
      · exact Or.inl he
      · exact Or.inr ⟨by have : k.val≠j.val := fun h => he (Fin.ext h); omega,hcut⟩
    · rintro (rfl | ⟨hk,hcut⟩)
      · refine ⟨le_rfl,?_⟩
        intro h hh
        simpa only [hpred h hh] using hr
      · exact ⟨by omega,hcut⟩

theorem cuts_card_successor {n : ℕ} (F : Set (Sym2 (Vertex n)))
    (i j : Fin n) (hij : i.val+1=j.val) :
    (cuts F j).card = (cuts F i).card + if rim i j ∈ F then 0 else 1 := by
  classical
  rw [cuts_successor F i j hij]
  have hj : j ∉ cuts F i := by simp only [cuts, Finset.mem_filter,
    Finset.mem_univ, true_and, not_and]; intro h; omega
  split_ifs <;> simp_all

noncomputable def componentLabel {n : ℕ} (F : Set (Sym2 (Vertex n))) :
    Vertex n → Option ℕ := by
  classical
  exact fun v => match v with
    | none => none
    | some i => if spoke i ∈ F then none else some (cuts F i).card

theorem label_rim {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : TriangleClosed F) {i j : Fin n} (hij : i.val+1=j.val)
    (hr : rim i j ∈ F) : componentLabel F (some i)=componentLabel F (some j) := by
  classical
  have hs := (hF i j hij).1 hr
  have hc := cuts_card_successor F i j hij
  simp only [hr, ite_true, Nat.add_zero] at hc
  simp only [componentLabel, hs, hc]

theorem label_preserved {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hsub : F ⊆ (graph n).edgeSet) (hF : TriangleClosed F)
    {v w : Vertex n} (h : (SimpleGraph.fromEdgeSet F).Adj v w) :
    componentLabel F v=componentLabel F w := by
  classical
  have he := ((SimpleGraph.fromEdgeSet_adj F).mp h).1
  have ha := hsub he
  cases v with
  | none =>
    cases w with
    | none => rfl
    | some j => simp only [componentLabel, show spoke j ∈ F from he, ite_true]
  | some i =>
    cases w with
    | none =>
      have hi : spoke i ∈ F := by simpa only [spoke, Sym2.eq_swap] using he
      simp only [componentLabel, hi, ite_true]
    | some j =>
      obtain hij | hji := ha
      · exact label_rim hF hij he
      · exact (label_rim hF hji (by simpa only [rim, Sym2.eq_swap] using he)).symm

theorem reachable_preserves_label {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hsub : F ⊆ (graph n).edgeSet) (hF : TriangleClosed F)
    {v w : Vertex n} (h : (SimpleGraph.fromEdgeSet F).Reachable v w) :
    componentLabel F v=componentLabel F w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (label_preserved hsub hF hadj).trans ih

theorem rim_of_label_eq {n : ℕ} {F : Set (Sym2 (Vertex n))}
    (hF : TriangleClosed F) {i j : Fin n} (hij : i.val+1=j.val)
    (he : componentLabel F (some i)=componentLabel F (some j)) : rim i j ∈ F := by
  classical
  by_cases hi : spoke i ∈ F
  · have hj : spoke j ∈ F := by
      by_contra hj
      simp [componentLabel,hi,hj] at he
    exact (hF i j hij).2 hi hj
  · by_cases hj : spoke j ∈ F
    · simp [componentLabel,hi,hj] at he
    · have hc : (cuts F i).card=(cuts F j).card := by
        simpa only [componentLabel,hi,hj,ite_false,Option.some.injEq] using he
      have hd := cuts_card_successor F i j hij
      by_contra hr
      simp only [hr,ite_false] at hd
      omega

/-- For fans, closure in every triangular face is sufficient for full graphic closure. -/
theorem isGraphicFlat_iff_triangleClosed {n : ℕ} {F : Set (Sym2 (Vertex n))} :
    IsGraphicFlat (graph n) F ↔ F ⊆ (graph n).edgeSet ∧ TriangleClosed F := by
  classical
  constructor
  · intro h
    exact ⟨h.1,h.triangleClosed⟩
  · rintro ⟨hsub,hF⟩
    refine ⟨hsub,?_⟩
    intro v w ha hr
    have he := reachable_preserves_label hsub hF hr
    cases v with
    | none =>
      cases w with
      | none => exact False.elim ha
      | some j =>
        change spoke j ∈ F
        by_contra hj
        simp [componentLabel,hj] at he
    | some i =>
      cases w with
      | none =>
        have hi : spoke i ∈ F := by
          by_contra hi
          simp [componentLabel,hi] at he
        simpa only [spoke,Sym2.eq_swap] using hi
      | some j =>
        obtain hij | hji := ha
        · exact rim_of_label_eq hF hij he
        · simpa only [rim,Sym2.eq_swap] using rim_of_label_eq hF hji he.symm

end Fan
