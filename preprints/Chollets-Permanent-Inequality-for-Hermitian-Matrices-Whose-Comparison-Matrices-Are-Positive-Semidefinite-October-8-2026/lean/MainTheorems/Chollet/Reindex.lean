import MainTheorems.Chollet.Regularization
import MainTheorems.Chollet.PermanentEquivalence

noncomputable section

namespace ResearchMain.Chollet

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] in
theorem comparison_submatrix (A : Matrix J J ℂ) (f : I → J)
    (hf : Function.Injective f) :
    comparison (A.submatrix f f) = (comparison A).submatrix f f := by
  funext i j
  simp [comparison, Matrix.submatrix, hf.eq_iff]

omit [Fintype I] [Fintype J] in
theorem ComparisonPSD.submatrix {A : Matrix J J ℂ} (hA : ComparisonPSD A)
    (f : I → J) (hf : Function.Injective f) : ComparisonPSD (A.submatrix f f) := by
  refine ⟨hA.1.submatrix f, ?_⟩
  rw [comparison_submatrix A f hf]
  exact hA.2.submatrix f

omit [Fintype I] [Fintype J] in
theorem ComparisonPD.submatrix {A : Matrix J J ℂ} (hA : ComparisonPD A)
    (f : I → J) (hf : Function.Injective f) : ComparisonPD (A.submatrix f f) := by
  refine ⟨hA.1.submatrix f, ?_⟩
  rw [comparison_submatrix A f hf]
  exact hA.2.submatrix hf

end ResearchMain.Chollet
