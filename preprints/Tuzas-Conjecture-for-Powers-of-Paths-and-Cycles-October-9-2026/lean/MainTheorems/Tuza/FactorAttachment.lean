import MainTheorems.Tuza.DecompositionTransport

namespace ResearchMain.Tuza

def factorFanGraph {V F : Type*} (M : PerfectFactors V F) : SimpleGraph (F ⊕ V) where
  Adj x y := match x, y with
    | .inl _, .inl _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr x, .inr y => M.unionGraph.Adj x y
  symm := ⟨by
    intro x y
    cases x <;> cases y
    all_goals try exact fun h => h
    exact fun h => h.symm⟩
  loopless := ⟨by intro x; cases x; exact fun h => h; exact M.unionGraph.irrefl⟩

theorem exists_factor_fan_decomposition {V F : Type*} [Fintype V] [Fintype F]
    [DecidableEq V] [DecidableEq F] (M : PerfectFactors V F) :
    Nonempty (TriangleDecomposition (factorFanGraph M)) := by
  classical
  let f : F ↪ F := Function.Embedding.refl F
  let P : PackingFamily (factorFanGraph M) (M.TriangleIndex f) := {
    triangle := fun i => fanTriangle i.val.1 i.val.2
    clique := fun i => by
      obtain ⟨⟨c, e⟩, he⟩ := i
      induction e using Sym2.inductionOn with
      | hf x y =>
        apply (factorFanGraph M).is3Clique_iff.mpr
        refine ⟨.inl c, .inr x, .inr y, trivial, trivial, ⟨c, he⟩, ?_⟩
        simp [fanTriangle, Sym2.toFinset_mk_eq]
    disjoint := fun i j hij => fanTriangle_disjoint M.graph f M.matching M.separated
      i.property j.property (fun h => hij (Subtype.ext h)) }
  refine ⟨⟨P.carrier, P.packing, ?_⟩⟩
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
    cases x with
    | inl c =>
      cases y with
      | inl d => exact False.elim hz
      | inr v =>
        obtain ⟨w, hw⟩ := M.perfect c v
        let i : M.TriangleIndex f := ⟨(c, s(v, w)), hw⟩
        refine mem_packingEdges.mpr ⟨fanTriangle c s(v, w),
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
        apply mem_triangleEdges.mpr
        simp
    | inr v =>
      cases y with
      | inl c =>
        obtain ⟨w, hw⟩ := M.perfect c v
        let i : M.TriangleIndex f := ⟨(c, s(v, w)), hw⟩
        refine mem_packingEdges.mpr ⟨fanTriangle c s(v, w),
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
        apply mem_triangleEdges.mpr
        simp
      | inr w =>
        obtain ⟨c, hc⟩ := hz
        let i : M.TriangleIndex f := ⟨(c, s(v, w)), hc⟩
        refine mem_packingEdges.mpr ⟨fanTriangle c s(v, w),
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
        apply mem_triangleEdges.mpr
        exact ⟨by simp, by simp, fun h => hc.ne (Sum.inr_injective h)⟩

theorem attach_factors {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (D : FactorDecomposition V F) : Nonempty (TriangleDecomposition (fanGraph F V)) := by
  classical
  obtain ⟨B⟩ := exists_factor_fan_decomposition D.factors
  obtain ⟨C⟩ := D.triangles.map (Function.Embedding.inr (α := F))
  have hdis : ∀ x y, (factorFanGraph D.factors).Adj x y →
      ¬(imageGraph (⊤ \ D.factors.unionGraph) Function.Embedding.inr).Adj x y := by
    intro x y hxy hxy'
    obtain ⟨u, v, rfl, rfl, huv⟩ := hxy'
    exact huv.2 hxy
  obtain ⟨T⟩ := B.join C hdis
  have he : factorFanGraph D.factors ⊔
      imageGraph (⊤ \ D.factors.unionGraph) (Function.Embedding.inr (α := F)) = fanGraph F V := by
    ext x y
    cases x with
    | inl c =>
      cases y <;> simp [factorFanGraph, fanGraph, imageGraph, Function.Embedding.inr]
    | inr v =>
      cases y with
      | inl c => simp [factorFanGraph, fanGraph, imageGraph, Function.Embedding.inr]
      | inr w =>
        change (D.factors.unionGraph.Adj v w ∨
          (imageGraph (⊤ \ D.factors.unionGraph) Function.Embedding.inr).Adj (.inr v) (.inr w)) ↔ v ≠ w
        have himage : (imageGraph (⊤ \ D.factors.unionGraph) (Function.Embedding.inr (α := F))).Adj
            (.inr v) (.inr w) ↔ v ≠ w ∧ ¬D.factors.unionGraph.Adj v w := by
          constructor
          · rintro ⟨a, b, ha, hb, hab⟩
            have he₁ : a = v := Sum.inr_injective ha
            have he₂ : b = w := Sum.inr_injective hb
            rwa [← he₁, ← he₂]
          · intro h
            exact ⟨v, w, rfl, rfl, h⟩
        rw [himage]
        have hn : D.factors.unionGraph.Adj v w → v ≠ w := fun h => h.ne
        tauto
  rw [he] at T
  exact ⟨T⟩

end ResearchMain.Tuza
