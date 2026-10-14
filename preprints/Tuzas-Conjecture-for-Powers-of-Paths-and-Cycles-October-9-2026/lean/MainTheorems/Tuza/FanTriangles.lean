import MainTheorems.Tuza.Constructions

namespace ResearchMain.Tuza

variable {C Q : Type*} [DecidableEq C] [DecidableEq Q]

def fanGraph (C Q : Type*) : SimpleGraph (C ⊕ Q) where
  Adj x y := match x, y with
    | .inl _, .inl _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr x, .inr y => x ≠ y
  symm := ⟨by intro x y; cases x <;> cases y <;> simp [ne_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def fanTriangle (c : C) (e : Sym2 Q) : Finset (C ⊕ Q) :=
  insert (.inl c) (e.toFinset.image Sum.inr)

@[simp]
theorem mem_fanTriangle_left (c d : C) (e : Sym2 Q) :
    Sum.inl d ∈ fanTriangle c e ↔ d = c := by
  simp [fanTriangle]

@[simp]
theorem mem_fanTriangle_right (c : C) (e : Sym2 Q) (q : Q) :
    Sum.inr q ∈ fanTriangle c e ↔ q ∈ e := by
  simp [fanTriangle]

theorem fanTriangle_clique (c : C) {e : Sym2 Q} (he : ¬e.IsDiag) :
    (fanGraph C Q).IsNClique 3 (fanTriangle c e) := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hxy : x ≠ y := by simpa using he
    apply (fanGraph C Q).is3Clique_iff.mpr
    refine ⟨.inl c, .inr x, .inr y, trivial, trivial, hxy, ?_⟩
    simp [fanTriangle, Sym2.toFinset_mk_eq]

omit [DecidableEq Q] in
theorem edge_unique_of_matching {M : SimpleGraph Q}
    (hm : ∀ x y z, M.Adj x y → M.Adj x z → y = z)
    {e f : Sym2 Q} {q : Q} (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet)
    (hqe : q ∈ e) (hqf : q ∈ f) : e = f := by
  obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hqe
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hqf
  exact congrArg (fun z => s(q, z)) (hm q x y he hf)

theorem fanTriangle_disjoint {F : Type*} (M : F → SimpleGraph Q) (f : C ↪ F)
    (hm : ∀ i x y z, (M i).Adj x y → (M i).Adj x z → y = z)
    (hs : ∀ i j x y, (M i).Adj x y → (M j).Adj x y → i = j)
    {c d : C} {e z : Sym2 Q} (he : e ∈ (M (f c)).edgeSet)
    (hz : z ∈ (M (f d)).edgeSet) (hne : (c, e) ≠ (d, z)) :
    Disjoint (triangleEdges (fanTriangle c e)) (triangleEdges (fanTriangle d z)) := by
  apply Finset.disjoint_left.mpr
  intro w hw₁ hw₂
  induction w using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨hx₁, hy₁, hxy⟩ := mem_triangleEdges.mp hw₁
    obtain ⟨hx₂, hy₂, _⟩ := mem_triangleEdges.mp hw₂
    cases x with
    | inl v =>
      have hc : v = c := mem_fanTriangle_left _ _ _ |>.mp hx₁
      have hd : v = d := mem_fanTriangle_left _ _ _ |>.mp hx₂
      have hcd : c = d := hc.symm.trans hd
      cases y with
      | inl v' =>
        have hv' : v' = c := mem_fanTriangle_left _ _ _ |>.mp hy₁
        exact hxy (congrArg Sum.inl (hc.trans hv'.symm))
      | inr q =>
        have hqe := mem_fanTriangle_right _ _ _ |>.mp hy₁
        have hqz := mem_fanTriangle_right _ _ _ |>.mp hy₂
        have hez := edge_unique_of_matching (hm (f c)) he (hcd ▸ hz) hqe hqz
        exact hne (Prod.ext hcd hez)
    | inr q =>
      cases y with
      | inl v =>
        have hc : v = c := mem_fanTriangle_left _ _ _ |>.mp hy₁
        have hd : v = d := mem_fanTriangle_left _ _ _ |>.mp hy₂
        have hcd : c = d := hc.symm.trans hd
        have hqe := mem_fanTriangle_right _ _ _ |>.mp hx₁
        have hqz := mem_fanTriangle_right _ _ _ |>.mp hx₂
        have hez := edge_unique_of_matching (hm (f c)) he (hcd ▸ hz) hqe hqz
        exact hne (Prod.ext hcd hez)
      | inr q' =>
        have hqq' : q ≠ q' := fun hh => hxy (congrArg Sum.inr hh)
        have heq : e = s(q, q') := (Sym2.mem_and_mem_iff hqq').mp
          ⟨(mem_fanTriangle_right _ _ _).mp hx₁, (mem_fanTriangle_right _ _ _).mp hy₁⟩
        have hzq : z = s(q, q') := (Sym2.mem_and_mem_iff hqq').mp
          ⟨(mem_fanTriangle_right _ _ _).mp hx₂, (mem_fanTriangle_right _ _ _).mp hy₂⟩
        have he' : s(q, q') ∈ (M (f c)).edgeSet := heq ▸ he
        have hz' : s(q, q') ∈ (M (f d)).edgeSet := hzq ▸ hz
        have hcd : c = d := f.injective (hs (f c) (f d) q q' he' hz')
        exact hne (Prod.ext hcd (heq.trans hzq.symm))

end ResearchMain.Tuza
