import CokernelPolynomiality.FamilyMatrix
import CokernelPolynomiality.IntervalFactorization
import CokernelPolynomiality.MinimalEndpointAntichain

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def familyActive {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => f ≫ intervalFamilyProj n m c d j ≠ 0)

@[simp] theorem mem_familyActive {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (j : Fin m) :
    j ∈ familyActive f ↔ f ≫ intervalFamilyProj n m c d j ≠ 0 := by
  classical
  simp [familyActive]

def familyElimination {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) :
    intervalFamily n m c d ⟶ intervalFamily n m c d := by
  classical
  exact intervalFamilyLift (fun j =>
    if hj : j ∈ familyActive f ∧ j ∉ R.P then
      intervalFamilyProj n m c d (R.pivot ⟨j,hj.1⟩).val ≫
        ((intervalScalar (f ≫ intervalFamilyProj n m c d j) hab hbn /
          intervalScalar (f ≫ intervalFamilyProj n m c d (R.pivot ⟨j,hj.1⟩).val) hab hbn) •
          intervalHom n (c (R.pivot ⟨j,hj.1⟩).val) (d (R.pivot ⟨j,hj.1⟩).val)
            (c j) (d j) (R.le_c ⟨j,hj.1⟩) (R.le_d ⟨j,hj.1⟩))
    else 0)

theorem familyElimination_proj_pivot {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) (j : Fin m) (hj : j ∈ R.P) :
    familyElimination f hab hbn R ≫ intervalFamilyProj n m c d j=0 := by
  classical
  simp [familyElimination,intervalFamilyLift_proj,hj]

theorem familyElimination_square {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) :
    familyElimination f hab hbn R ≫ familyElimination f hab hbn R=0 := by
  classical
  apply intervalFamily_hom_ext
  intro j
  rw [Category.assoc]
  conv_lhs => rhs; unfold familyElimination; rw [intervalFamilyLift_proj]
  by_cases hj : j ∈ familyActive f ∧ j ∉ R.P
  · rw [dite_eq_left hj,← Category.assoc,
      familyElimination_proj_pivot f hab hbn R _ (R.pivot ⟨j,hj.1⟩).property,zero_comp,zero_comp]
  · rw [dite_eq_right hj,comp_zero,zero_comp]

theorem familyElimination_source {n m a b : ℕ} {c d : Fin m → ℕ}
    (f : intervalRep n a b ⟶ intervalFamily n m c d) (hab : a ≤ b) (hbn : b ≤ n)
    (R : EndpointReduction m (familyActive f) c d) (j : Fin m) (hj : j ∉ R.P) :
    f ≫ familyElimination f hab hbn R ≫ intervalFamilyProj n m c d j=
      f ≫ intervalFamilyProj n m c d j := by
  classical
  unfold familyElimination
  rw [intervalFamilyLift_proj]
  by_cases hs : j ∈ familyActive f
  · rw [dite_eq_left ⟨hs,hj⟩,← Category.assoc]
    exact interval_factor_through _ _ hab hbn
      ((mem_familyActive f _).mp (R.subset (R.pivot ⟨j,hs⟩).property))
      ((mem_familyActive f j).mp hs) (R.le_c ⟨j,hs⟩) (R.le_d ⟨j,hs⟩)
  · rw [dite_eq_right (by simp [hs]),comp_zero]
    symm
    by_contra hf
    exact hs ((mem_familyActive f j).mpr hf)

end CokernelPolynomiality
