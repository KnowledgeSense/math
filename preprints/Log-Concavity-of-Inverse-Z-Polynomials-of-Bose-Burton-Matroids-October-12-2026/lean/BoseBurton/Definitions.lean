import BoseBurton.VectorMatroidRank
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Independence

noncomputable section
namespace BoseBurton
open Set Submodule Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

/-- Projective geometry on actual one-dimensional vector directions. -/
def projectiveMatroid (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Finite V] : Matroid (ℙ K V) :=
  vectorMatroid (K := K) Projectivization.rep

/-- All projective points surviving deletion of the projective subspace of `W`. -/
def survivingPoints (W : Submodule K V) : Set (ℙ K V) :=
  {p | p.rep ∉ W}

/-- The Bose–Burton matroid is the literal restriction of projective geometry. -/
def matroid (W : Submodule K V) : Matroid (ℙ K V) :=
  (projectiveMatroid K V).restrict (survivingPoints W)

/-- The surviving points in a vector subspace. -/
def pointsIn (W U : Submodule K V) : Set (ℙ K V) :=
  {p | p.rep ∈ U ∧ p.rep ∉ W}

@[simp] theorem matroid_ground (W : Submodule K V) :
    (matroid W).E = survivingPoints W := rfl

omit [Module.Finite K V] [Finite V] in
theorem survivingPoints_iff (W : Submodule K V) (p : ℙ K V) :
    p ∈ survivingPoints W ↔ ¬ p.submodule ≤ W := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

@[simp] theorem matroid_indep (W : Submodule K V) (I : Set (ℙ K V)) :
    (matroid W).Indep I ↔ LinearIndepOn K Projectivization.rep I ∧ I ⊆ survivingPoints W := by
  rw [matroid, Matroid.restrict_indep_iff, projectiveMatroid, vectorMatroid_indep]

/-- Rank on every surviving point set is the dimension of its actual vector span. -/
theorem matroid_eRk (W : Submodule K V) (X : Set (ℙ K V))
    (hX : X ⊆ survivingPoints W) :
    (matroid W).eRk X = (finrank K (vectorSpan (K := K) Projectivization.rep X) : ℕ∞) := by
  rw [matroid, Matroid.restrict_eRk_eq _ hX, projectiveMatroid, vectorMatroid_eRk]

theorem matroid_mem_closure (W : Submodule K V) (X : Set (ℙ K V))
    (hX : X ⊆ survivingPoints W) (p : ℙ K V) :
    p ∈ (matroid W).closure X ↔
      p.rep ∈ vectorSpan (K := K) Projectivization.rep X ∧ p.rep ∉ W := by
  rw [matroid, Matroid.restrict_closure_eq _ hX (subset_univ _)]
  change (p ∈ (vectorMatroid (K := K) Projectivization.rep).closure X ∧ _) ↔ _
  rw [vectorMatroid_mem_closure]
  rfl

end BoseBurton
