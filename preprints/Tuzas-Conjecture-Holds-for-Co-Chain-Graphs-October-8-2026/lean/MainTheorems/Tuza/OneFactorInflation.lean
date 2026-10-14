import MainTheorems.Tuza.MatchingCoordinates

namespace ResearchMain.Tuza

theorem PerfectFactors.one_union {V : Type*} (M : PerfectFactors V (Fin 1)) :
    M.unionGraph = M.graph 0 := by
  ext x y
  constructor
  · rintro ⟨i, hi⟩
    have he : i = 0 := Subsingleton.elim _ _
    rwa [he] at hi
  · intro h
    exact ⟨0, h⟩

theorem complete_pair_complement {I : Type*} :
    (⊤ : SimpleGraph (I × Fin 2)) \ fiberGraph (I := I) (⊤ : SimpleGraph (Fin 2)) =
      crossGraph (⊤ : SimpleGraph I) (Fin 2) := by
  ext x y
  change (x ≠ y ∧ ¬(x.1 = y.1 ∧ x.2 ≠ y.2)) ↔ x.1 ≠ y.1
  constructor
  · rintro ⟨hne, hnot⟩ he
    have hlabels : x.2 ≠ y.2 := fun h => hne (Prod.ext he h)
    exact hnot ⟨he, hlabels⟩
  · intro he
    exact ⟨fun h => he (congrArg Prod.fst h), fun h => he h.1⟩

theorem inflate_one_factor_decomposition {V Q F : Type*} [Fintype V] [DecidableEq V]
    [Fintype Q] [DecidableEq Q] [AddCommGroup Q]
    (D : FactorDecomposition V (Fin 1)) (E : FactorDecomposition (Fin 2 × Q) F) :
    Nonempty (FactorDecomposition (V × Q) F) := by
  classical
  obtain ⟨k, ⟨e⟩⟩ := perfect_matching_coordinates (D.factors.graph 0)
    (D.factors.matching 0) (D.factors.perfect 0)
  let g : ((⊤ : SimpleGraph (Fin k × Fin 2)) \ fiberGraph (⊤ : SimpleGraph (Fin 2))) ≃g
      (⊤ \ D.factors.unionGraph) := {
    toEquiv := e.toEquiv
    map_rel_iff' := by
      intro x y
      change (e x ≠ e y ∧ ¬D.factors.unionGraph.Adj (e x) (e y)) ↔
        x ≠ y ∧ ¬(fiberGraph (⊤ : SimpleGraph (Fin 2))).Adj x y
      rw [D.factors.one_union, e.map_rel_iff]
      exact and_congr (not_congr e.injective.eq_iff) Iff.rfl }
  obtain ⟨A⟩ := D.triangles.congr g.symm
  rw [complete_pair_complement] at A
  obtain ⟨B⟩ := exists_blowup_decomposition (Q := Q) A
  let h : crossGraph (crossGraph (⊤ : SimpleGraph (Fin k)) (Fin 2)) Q ≃g
      crossGraph (⊤ : SimpleGraph (Fin k)) (Fin 2 × Q) := {
    toEquiv := Equiv.prodAssoc (Fin k) (Fin 2) Q
    map_rel_iff' := by intro x y; rfl }
  obtain ⟨C⟩ := B.congr h
  obtain ⟨T⟩ := factor_decomposition_of_cross C E
  let f : (Fin k × (Fin 2 × Q)) ≃ (V × Q) :=
    (Equiv.prodAssoc (Fin k) (Fin 2) Q).symm.trans
      (Equiv.prodCongr e.toEquiv (Equiv.refl Q))
  exact T.congr f (Equiv.refl F)

end ResearchMain.Tuza
