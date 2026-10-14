import Dowling.ActualApexWeightsDefinitions

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Subsingleton G] {n : ℕ}

/-- The last-coloop boundary and Pascal telescoping yield the source positive
correction identity without importing a separate formal-series formula. -/
theorem apex_full_correction_identity (hn : 2≤n) :
    fullY G n-C (n : ℤ)*jointDelta G n=missingJointCorrection G n n := by
  let i : Fin n := ⟨0,by omega⟩
  have h := retained_trivial_identity (G := G) ({i} : Set (Fin n)) ⟨i,Set.mem_singleton i⟩
  rw [configurationY_single_joint] at h
  simp only [Set.toFinset_singleton,Finset.card_singleton] at h
  have hp : missingJointCorrection G n n=missingJointCorrection G n (n-1)+missingJointIncrement G n (n-1) := by
    have hs := missingJointCorrection_succ (G := G) (n := n) (n-1)
    simpa only [show n-1+1=n by omega] using hs
  have hd : jointDelta G n=(1+Polynomial.X)*fullY G (n-1)-missingJointIncrement G n (n-1) := rfl
  rw [hd] at h
  rw [hp,hd]
  rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one,map_sub,map_one] at h
  linear_combination -h

/-- Cleared-denominator positive decomposition of every actual partial-apex
matroid, including the full and single-joint endpoints. -/
theorem apex_positive_decomposition_cleared (hn : 2≤n) (X : Set (Fin n)) (hX : X.Nonempty) :
    C (n : ℤ)*configurationY (G := G) X=
      C (X.toFinset.card : ℤ)*fullY G n+
      C ((n-X.toFinset.card : ℕ) : ℤ)*missingJointCorrection G n n-
      C (n : ℤ)*missingJointCorrection G n (n-X.toFinset.card) := by
  rw [retained_trivial_identity X hX,← apex_full_correction_identity hn]
  have hk : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  rw [Nat.cast_sub hk,map_sub]
  ring

end Dowling
