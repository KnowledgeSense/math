import MainTheorems.Chollet.RankCoefficients.ColumnContraction

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem quotient_columnProduct_linear (A : Matrix I I ℂ) :
    Ideal.Quotient.mk (squareIdeal I) (columnProduct A) =
      ∏ j, linearForm (fun i => A i j) := by
  simp only [columnProduct, linearForm, map_prod, map_sum, map_mul, scalar, rowVariable]

theorem permanent_fixed_zero (A : Matrix I I ℂ) (s : Finset I)
    (h : (∏ j ∈ s, linearForm (fun i => A i j)) = 0) : A.permanent = 0 := by
  have hs : (∏ j, linearForm (fun i => A i j)) =
      (∏ j ∈ s, linearForm (fun i => A i j)) *
        ∏ j ∈ Finset.univ \ s, linearForm (fun i => A i j) := by
    rw [← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have he : scalar A.permanent * monomial (Finset.univ : Finset I) =
      scalar 0 * monomial (Finset.univ : Finset I) := by
    rw [← quotient_columnProduct, quotient_columnProduct_linear, hs, h, zero_mul,
      scalar_zero, zero_mul]
  exact scalar_monomial_injective Finset.univ _ _ he

theorem permanent_fixed_columns (A : Matrix I I ℂ) (s : Finset I)
    (p : RootedPartition I) (c : ℂ)
    (h : (∏ j ∈ s, linearForm (fun i => A i j)) = scalar c * p.polynomial)
    (e : p.parts ≃ {i : I // i ∉ s}) :
    A.permanent = c * (p.contractionMatrix (fun i t => A i (e t))).permanent := by
  let Q : Matrix I p.parts ℂ := fun i t => A i (e t)
  have hrest : (∏ j ∈ Finset.univ \ s, linearForm (fun i => A i j)) =
      ∏ t : p.parts, linearForm (fun i => Q i t) := by
    have hp : (∏ j : {i : I // i ∉ s}, linearForm (fun i => A i j)) =
        ∏ j ∈ Finset.univ \ s, linearForm (fun i => A i j) := by
      exact (Finset.prod_subtype (Finset.univ \ s) (fun _ => by simp)
        (fun j => linearForm (fun i => A i j))).symm
    rw [← hp]
    symm
    exact Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hs : (∏ j, linearForm (fun i => A i j)) =
      (∏ j ∈ s, linearForm (fun i => A i j)) *
        ∏ j ∈ Finset.univ \ s, linearForm (fun i => A i j) := by
    rw [← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have he : scalar A.permanent * monomial (Finset.univ : Finset I) =
      scalar (c * (p.contractionMatrix Q).permanent) * monomial (Finset.univ : Finset I) := by
    rw [← quotient_columnProduct, quotient_columnProduct_linear, hs, h, hrest, scalar_mul]
    rw [mul_assoc, p.column_contraction Q]
    ring
  exact scalar_monomial_injective Finset.univ _ _ he

end ResearchMain.Chollet.RankCoefficients


