import Dowling.ConstraintRankCard
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Minor.Restrict

noncomputable section
namespace Dowling
open Set
variable (G : Type*) [Group G] [Finite G] (n : ℕ)

/-- The genuine finite gain matroid. Augmentation is proved from the exact solution counts. -/
def fullMatroid : Matroid (Edge G n) :=
  (IndepMatroid.ofBddAugment univ EquationIndep
    equationIndep_empty
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun _ _ hI hJ hc => equationIndep_augment hI hJ hc)
    ⟨n, fun I hI => by
      rw [← I.toFinite.cast_ncard_eq]
      have h := constraintRank_le I
      rw [hI] at h
      exact_mod_cast h⟩
    (fun _ _ => subset_univ _)).matroid

@[simp] theorem fullMatroid_ground : (fullMatroid G n).E = univ := rfl
@[simp] theorem fullMatroid_indep (I : Set (Edge G n)) :
    (fullMatroid G n).Indep I ↔ EquationIndep I := Iff.rfl

/-- Keep all gain links and exactly the specified joints. -/
def matroid (X : Set (Fin n)) : Matroid (Edge G n) := (fullMatroid G n).restrict (ground G n X)

@[simp] theorem matroid_ground (X : Set (Fin n)) : (matroid G n X).E = ground G n X := rfl

end Dowling
