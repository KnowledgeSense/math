import MainTheorems.AHOConstants.PositiveTrace
import MainTheorems.AHOConstants.Interpolation
import MainTheorems.AHOConstants.BoundaryPowers
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

structure WeightedFactor (I : Type*) [Fintype I] [DecidableEq I] where
  positiveMatrix : Matrix I I ℂ
  unitaryMatrix : Matrix I I ℂ
  weight : ℝ
  positiveDefinite : positiveMatrix.PosDef
  unitaryMembership : unitaryMatrix ∈ unitary (Matrix I I ℂ)

noncomputable def factorValue (f : WeightedFactor I) : Matrix I I ℂ :=
  f.unitaryMatrix * spectralPower f.positiveMatrix f.weight

noncomputable def factorBound (f : WeightedFactor I) : ℝ :=
  (Matrix.trace f.positiveMatrix).re ^ f.weight

noncomputable def weightedProduct (fs : List (WeightedFactor I)) : Matrix I I ℂ :=
  (fs.map factorValue).prod

noncomputable def weightedBound (fs : List (WeightedFactor I)) : ℝ :=
  (fs.map factorBound).prod

def totalWeight (fs : List (WeightedFactor I)) : ℝ := (fs.map WeightedFactor.weight).sum

theorem totalWeight_cons (f : WeightedFactor I) (fs : List (WeightedFactor I)) :
    totalWeight (f :: fs) = f.weight + totalWeight fs := rfl

theorem weightedProduct_cons (f : WeightedFactor I) (fs : List (WeightedFactor I)) :
    weightedProduct (f :: fs) = factorValue f * weightedProduct fs := rfl

theorem weightedBound_cons (f : WeightedFactor I) (fs : List (WeightedFactor I)) :
    weightedBound (f :: fs) = factorBound f * weightedBound fs := rfl

theorem totalWeight_nonneg {fs : List (WeightedFactor I)}
    (hf : ∀ f ∈ fs, 0 ≤ f.weight) : 0 ≤ totalWeight fs := by
  apply List.sum_nonneg
  intro w hw
  obtain ⟨f, hfs, rfl⟩ := List.mem_map.mp hw
  exact hf f hfs

theorem weight_le_total {fs : List (WeightedFactor I)}
    (hf : ∀ f ∈ fs, 0 ≤ f.weight) {f : WeightedFactor I} (hfm : f ∈ fs) :
    f.weight ≤ totalWeight fs := by
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨f, hfm, rfl⟩)
  intro w hw
  obtain ⟨g, hgs, rfl⟩ := List.mem_map.mp hw
  exact hf g hgs

theorem totalWeight_pos {fs : List (WeightedFactor I)}
    (hf : ∀ f ∈ fs, 0 < f.weight) (hne : fs ≠ []) : 0 < totalWeight fs := by
  cases fs with
  | nil => exact False.elim (hne rfl)
  | cons f fs =>
    rw [totalWeight_cons]
    exact add_pos_of_pos_of_nonneg (hf f (by simp))
      (totalWeight_nonneg (fun g hg => (hf g (by simp [hg])).le))

theorem differentiable_list_product (fs : List (ℂ → Matrix I I ℂ))
    (hf : ∀ f ∈ fs, Differentiable ℂ f) :
    Differentiable ℂ (fun z => (fs.map (fun f => f z)).prod) := by
  revert hf
  induction fs with
  | nil => intro _; simpa only [List.map_nil, List.prod_nil] using
      differentiable_const (c := (1 : Matrix I I ℂ))
  | cons f fs ih =>
    intro hf
    simpa only [List.map_cons, List.prod_cons] using
      (hf f (by simp)).fun_mul (ih (fun g hg => hf g (by simp [hg])))

theorem unitary_list_product (xs : List (Matrix I I ℂ))
    (hx : ∀ x ∈ xs, x ∈ unitary (Matrix I I ℂ)) :
    xs.prod ∈ unitary (Matrix I I ℂ) := by
  revert hx
  induction xs with
  | nil => intro _; exact (unitary (Matrix I I ℂ)).one_mem
  | cons x xs ih =>
    intro hx
    exact (unitary (Matrix I I ℂ)).mul_mem (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))

noncomputable def normalizedFactor (θ : ℝ) (z : ℂ) (f : WeightedFactor I) :
    WeightedFactor I where
  positiveMatrix := f.positiveMatrix
  unitaryMatrix := f.unitaryMatrix * complexPower f.positiveDefinite
    (((z * (f.weight / θ : ℝ)).im : ℂ) * Complex.I)
  weight := f.weight / θ
  positiveDefinite := f.positiveDefinite
  unitaryMembership := (unitary (Matrix I I ℂ)).mul_mem f.unitaryMembership
    (complexPower_imaginary_unitary f.positiveDefinite _)

theorem normalized_totalWeight (θ : ℝ) (z : ℂ) (fs : List (WeightedFactor I)) :
    totalWeight (fs.map (normalizedFactor θ z)) = totalWeight fs / θ := by
  induction fs with
  | nil => simp [totalWeight]
  | cons f fs ih =>
    simp only [List.map_cons, totalWeight_cons, normalizedFactor, ih]
    exact (add_div _ _ _).symm

theorem normalized_weightedBound (θ : ℝ) (z : ℂ) (fs : List (WeightedFactor I)) :
    weightedBound (fs.map (normalizedFactor θ z)) =
      (fs.map (fun f => (Matrix.trace f.positiveMatrix).re ^ (f.weight / θ))).prod := by
  simp only [weightedBound, List.map_map, factorBound, normalizedFactor, Function.comp_def]

theorem normalized_bound_power [Nonempty I] {θ : ℝ} (hθ : θ ≠ 0)
    (z : ℂ) (fs : List (WeightedFactor I)) :
    weightedBound (fs.map (normalizedFactor θ z)) ^ θ = weightedBound fs := by
  rw [normalized_weightedBound]
  induction fs with
  | nil => simp [weightedBound]
  | cons f fs ih =>
    simp only [List.map_cons, List.prod_cons, weightedBound_cons]
    have hp := positive_trace_pos f.positiveDefinite
    have ht : 0 ≤ (fs.map (fun g : WeightedFactor I =>
        (Matrix.trace g.positiveMatrix).re ^ (g.weight / θ))).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact (Real.rpow_pos_of_pos (positive_trace_pos g.positiveDefinite) _).le
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hp _).le ht, ih,
      ← Real.rpow_mul hp.le, div_mul_cancel₀ _ hθ]
    rfl

end ResearchMain.AHOConstants
