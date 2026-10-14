import MainTheorems.PreorderGamma.RootLattice

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def integerRootVertex (i j : Option E) : (Option E → ℤ) × (Option E → ℤ) :=
  (Pi.single i 1, Pi.single j 1)

abbrev TransportCells {u v : Option E → ℕ}
    (p : NaturalTransport augmentedRelation u v) :=
  Σ e : Option E × Option E, Fin (p.flow e.1 e.2)

noncomputable def transportCellEdge {u v : Option E → ℕ}
    (p : NaturalTransport augmentedRelation u v) (c : TransportCells p) : AugmentedEdge E :=
  ⟨c.1, by
    by_contra h
    have hz := p.supported c.1.1 c.1.2 h
    have hpos : 0 < p.flow c.1.1 c.1.2 :=
      Nat.lt_of_le_of_lt (Nat.zero_le c.2.val) c.2.isLt
    omega⟩

omit [DecidableEq E] in
theorem transportCells_card {u v : Option E → ℕ}
    (p : NaturalTransport augmentedRelation u v) :
    Fintype.card (TransportCells p) = ∑ i, u i := by
  simp only [Fintype.card_sigma, Fintype.card_fin, Fintype.sum_prod_type, p.row_sum]

theorem transportCells_vertex_sum {u v : Option E → ℕ}
    (p : NaturalTransport augmentedRelation u v) :
    (∑ c : TransportCells p,
      integerRootVertex (transportCellEdge p c).val.1 (transportCellEdge p c).val.2) =
        ((fun i => (u i : ℤ)), fun j => (v j : ℤ)) := by
  classical
  apply Prod.ext
  · funext i
    simp only [Prod.fst_sum, integerRootVertex, transportCellEdge,
      Finset.sum_apply, Pi.single_apply]
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ e : Option E × Option E,
          if i = e.1 then (p.flow e.1 e.2 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : i = e.1 <;> simp [h]
      _ = _ := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Nat.cast_sum, p.row_sum]
  · funext j
    simp only [Prod.snd_sum, integerRootVertex, transportCellEdge,
      Finset.sum_apply, Pi.single_apply]
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ e : Option E × Option E,
          if j = e.2 then (p.flow e.1 e.2 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : j = e.2 <;> simp [h]
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Nat.cast_sum, p.column_sum]

theorem root_integer_decomposition (t : ℕ)
    (z : (Option E → ℤ) × (Option E → ℤ)) (hz : RootIntegerPoints t z) :
    ∃ f : Fin t → AugmentedEdge E,
      z = ∑ i : Fin t, integerRootVertex (f i).val.1 (f i).val.2 := by
  classical
  let q := rootIntegerNaturalEquiv t ⟨z, hz⟩
  obtain ⟨p⟩ := q.property.2.2
  have hcard : Fintype.card (TransportCells p) = t := by
    rw [transportCells_card p, q.property.1]
  let e : TransportCells p ≃ Fin t := Fintype.equivFinOfCardEq hcard
  refine ⟨fun i => transportCellEdge p (e.symm i), ?_⟩
  calc
    z = ((fun i => (q.val.1 i : ℤ)), fun j => (q.val.2 j : ℤ)) := by
      apply Prod.ext <;> funext i
      · exact (Int.toNat_of_nonneg ((rootIntegerPoints_nonnegative hz).1 i)).symm
      · exact (Int.toNat_of_nonneg ((rootIntegerPoints_nonnegative hz).2 i)).symm
    _ = ∑ c : TransportCells p,
        integerRootVertex (transportCellEdge p c).val.1 (transportCellEdge p c).val.2 :=
      (transportCells_vertex_sum p).symm
    _ = _ := by
      apply Fintype.sum_equiv e
      intro c
      simp only [e.symm_apply_apply]

omit [Fintype E] in
theorem integerRootVertex_mem (e : AugmentedEdge E) :
    RootIntegerPoints 1 (integerRootVertex e.val.1 e.val.2) := by
  apply Set.mem_smul_set.mpr
  refine ⟨rootVertex e.val.1 e.val.2, rootVertex_mem_rootPolytope e, ?_⟩
  ext <;> simp [integerRootVertex, rootVertex, Pi.single_apply]

theorem root_integer_points_one_iff
    (z : (Option E → ℤ) × (Option E → ℤ)) :
    RootIntegerPoints 1 z ↔
      ∃ e : AugmentedEdge E, z = integerRootVertex e.val.1 e.val.2 := by
  constructor
  · intro hz
    obtain ⟨f, hf⟩ := root_integer_decomposition 1 z hz
    refine ⟨f 0, ?_⟩
    simpa using hf
  · rintro ⟨e, rfl⟩
    exact integerRootVertex_mem e

end ResearchMain.PreorderGamma
