import MeanMaximumForests.Positivity
import MeanMaximumForests.ProductChecks00
import MeanMaximumForests.ProductChecks01
import MeanMaximumForests.ProductChecks11
import MeanMaximumForests.RootChecks

namespace MeanMaximumForests.Release

def releaseGenerators (f : Bool) : Set ConeVector :=
  if f then generatorSet generators1 else generatorSet generators0

def releaseCone (f : Bool) : Set ConeVector := {v | GeneratedCone (releaseGenerators f) v}

theorem empty_generator : unitVector ∈ releaseGenerators false := by
  refine ⟨⟨29, by decide⟩, ?_⟩
  ext <;> norm_num [generators0, generators0Array, IntegerVector.toReal, unitVector]

theorem all_products : ∀ f g v, v ∈ releaseGenerators f → ∀ w, w ∈ releaseGenerators g →
    GeneratedCone (releaseGenerators (f || g)) (product v w) := by
  intro f g
  cases f <;> cases g
  · rintro v ⟨i, rfl⟩ w ⟨j, rfl⟩
    exact product00_mem i j
  · rintro v ⟨i, rfl⟩ w ⟨j, rfl⟩
    exact product01_mem i j
  · rintro v ⟨i, rfl⟩ w ⟨j, rfl⟩
    rw [product_comm]
    exact product01_mem j i
  · rintro v ⟨i, rfl⟩ w ⟨j, rfl⟩
    exact product11_mem i j

theorem all_roots : ∀ f v, v ∈ releaseGenerators f →
    GeneratedCone (releaseGenerators (!f)) (plant (47 / 100) f v) := by
  intro f
  cases f
  · rintro v ⟨i, rfl⟩
    exact root0_mem i
  · rintro v ⟨i, rfl⟩
    exact root1_mem i

theorem all_signs : ∀ f v, v ∈ releaseGenerators f →
    0 ≤ (plant (47 / 100) f v).x := by
  intro f
  cases f
  · rintro v ⟨i, rfl⟩
    exact root_sign_real _ _ (root0_sign i)
  · rintro v ⟨i, rfl⟩
    exact root_sign_real _ _ (root1_sign i)

theorem release_invariant : InvariantConditions (47 / 100) releaseCone :=
  invariant_of_generator_checks _ releaseGenerators empty_generator all_products all_roots all_signs

theorem release_root_nonnegative (F : ForestExpr) : 0 ≤ (vector (47 / 100) (.root F)).x :=
  root_nonnegative release_invariant F

theorem release_forest_nonnegative (F : ForestExpr) : 0 ≤ (vector (47 / 100) F).x :=
  forest_nonnegative release_invariant F

end MeanMaximumForests.Release
