import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Basic.Real.Basic

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators

theorem sum_injection_support {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (he : Function.Injective e) (f : ι → ℝ)
    (hf : ∀ i, i ∉ Set.range e → f i = 0) :
    ∑ i, f i = ∑ k, f (e k) := by
  classical
  calc
    ∑ i, f i = ∑ i ∈ Finset.univ.image e, f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      apply hf i
      rintro ⟨k, rfl⟩
      exact hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    _ = _ := Finset.sum_image he.injOn

theorem quadratic_submatrix_support {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (he : Function.Injective e) (T : Matrix ι ι ℝ) (v : ι → ℝ)
    (hv : ∀ i, i ∉ Set.range e → v i = 0) :
    v ⬝ᵥ (T *ᵥ v) = (v ∘ e) ⬝ᵥ (T.submatrix e e *ᵥ (v ∘ e)) := by
  change (∑ i, v i * (∑ j, T i j * v j)) =
    ∑ i, v (e i) * (∑ j, T (e i) (e j) * v (e j))
  rw [sum_injection_support e he _ (fun i hi => by rw [hv i hi, zero_mul])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_injection_support e he _ (fun j hj => by rw [hv j hj, mul_zero])]

end ResearchMain.WishartBlocks
