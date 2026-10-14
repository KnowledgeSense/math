import HardCoreActivityThreshold.RootOdds

/-! Exact weighted deletion and disjoint-union identities for arbitrary finite graphs. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

noncomputable def partitionWithin (G : SimpleGraph V) (activity : V → ℝ) (vertices : Finset V) : ℝ :=
  ∑ s ∈ Forest.independentSetsWithin G vertices, ∏ v ∈ s, activity v

omit [DecidableEq V] in
@[simp] theorem partitionWithin_empty (G : SimpleGraph V) (activity : V → ℝ) :
    partitionWithin G activity ∅ = 1 := by
  simp [partitionWithin]

omit [DecidableEq V] in
theorem partitionWithin_pos (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (vertices : Finset V) : 0 < partitionWithin G activity vertices := by
  apply sum_pos'
  · intro s _
    exact (prod_pos (fun v _ => ha v)).le
  · exact ⟨∅, (Forest.mem_independentSetsWithin G).mpr ⟨empty_subset _, Forest.independent_empty G⟩,
      by simp⟩

theorem partitionWithin_recursion (G : SimpleGraph V) (activity : V → ℝ)
    (vertices : Finset V) (r : V) (hr : r ∈ vertices) :
    partitionWithin G activity vertices = partitionWithin G activity (vertices.erase r) +
      activity r * partitionWithin G activity (Forest.compatibleVertices G vertices r) := by
  unfold partitionWithin
  rw [Forest.independentSetsWithin_decomposition G vertices r hr,
    sum_union (Forest.independent_decomposition_disjoint G vertices r),
    sum_image (Forest.insert_injective_on_compatible G vertices r)]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro s hs
  have hrs : r ∉ s := fun h => Forest.compatible_not_mem G vertices r
    (((Forest.mem_independentSetsWithin G).mp hs).1 h)
  exact prod_insert hrs

theorem partitionWithin_union (G : SimpleGraph V) (activity : V → ℝ)
    {a b : Finset V} (hd : Disjoint a b) (he : Forest.Separated G a b) :
    partitionWithin G activity (a ∪ b) = partitionWithin G activity a * partitionWithin G activity b := by
  unfold partitionWithin
  rw [Forest.independentSetsWithin_union G he,
    sum_image (Forest.union_injective_on_independentSets G hd), sum_mul_sum, sum_product]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro t ht
  exact prod_union (hd.mono ((Forest.mem_independentSetsWithin G).mp hs).1
    ((Forest.mem_independentSetsWithin G).mp ht).1)

variable [Fintype V]

omit [DecidableEq V] in
theorem partitionWithin_univ (G : SimpleGraph V) (activity : V → ℝ) :
    partitionWithin G activity univ = partitionFunction G activity := by
  unfold partitionWithin partitionFunction
  have he : Forest.independentSetsWithin G univ = univ.filter (Independent G) := by
    ext s
    simp only [Forest.mem_independentSetsWithin, subset_univ, true_and, mem_filter, mem_univ]
    rfl
  rw [he, sum_filter]
  rfl

/-- Absence of a vertex is exactly the hard-core partition ratio on the deleted graph. -/
theorem hardCore_absence_partition (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) :
    (hardCoreLaw G activity ha).eventMass (fun s => v ∉ s) =
      partitionWithin G activity (univ.erase v) / partitionFunction G activity := by
  unfold FiniteLaw.eventMass partitionWithin
  have he : Forest.independentSetsWithin G (univ.erase v) =
      univ.filter (fun s => Independent G s ∧ v ∉ s) := by
    ext s
    simp only [Forest.mem_independentSetsWithin, mem_filter, mem_univ, true_and]
    have hsub : s ⊆ univ.erase v ↔ v ∉ s := by simp [subset_erase]
    rw [hsub]
    change (v ∉ s ∧ Independent G s) ↔ (Independent G s ∧ v ∉ s)
    tauto
  rw [he, sum_filter, sum_div]
  apply sum_congr rfl
  intro s _
  by_cases hi : Independent G s <;> by_cases hv : v ∈ s <;>
    simp [hardCoreLaw_mass, configurationWeight, hi, hv]

/-- The exact occupation odds are a ratio of actual weighted partition functions. -/
theorem hardCore_occupation_odds (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) :
    marginal (hardCoreLaw G activity ha) v / (1-marginal (hardCoreLaw G activity ha) v) =
      activity v * partitionWithin G activity (Forest.compatibleVertices G univ v) /
        partitionWithin G activity (univ.erase v) := by
  have hr := partitionWithin_recursion G activity univ v (mem_univ v)
  rw [partitionWithin_univ] at hr
  have habs := hardCore_absence_partition G activity ha v
  rw [absent_eventMass] at habs
  have hz := (partitionFunction_pos G activity (fun v => (ha v).le)).ne'
  have hd := (partitionWithin_pos G activity ha (univ.erase v)).ne'
  have hm := hardCore_marginal_lt_one G activity ha v
  have hmn : 1-marginal (hardCoreLaw G activity ha) v ≠ 0 := by linarith
  apply (div_eq_iff hmn).mpr
  field_simp at habs ⊢
  nlinarith [habs]

end HardCoreActivityThreshold
