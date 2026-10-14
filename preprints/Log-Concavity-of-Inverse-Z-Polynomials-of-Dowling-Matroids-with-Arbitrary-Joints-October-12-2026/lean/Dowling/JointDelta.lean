import Dowling.JointCorrectionSumNontrivial

noncomputable section
namespace Dowling
open Finset Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

/-- The common one-joint decrement, built from actual full-Dowling invariants. -/
def jointDelta (G : Type*) [Group G] [Fintype G] (n : ℕ) : Polynomial ℤ :=
  (1+Polynomial.X)*fullY G (n-1)-
    ∑ r∈range (n+1),C (((n-1).choose (r-1) : ℕ) : ℤ)*jointRankCorrection G n r

theorem joint_correction_sum_nontrivial_choose [Nontrivial G] (i : Fin n) (hiX : i∈X) :
    (∑ p : Configuration G X,if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0)=
      ∑ r∈range (n+1),C (((n-1).choose (r-1) : ℕ) : ℤ)*jointRankCorrection G n r := by
  rw [joint_correction_sum_nontrivial i hiX]
  apply sum_congr rfl
  intro r hr
  by_cases hz : r=0
  · simp [hz,jointRankCorrection]
  · rw [jointZeroSets_card i r (by omega)]
    simp

theorem joint_deletion_nontrivial [Nontrivial G] (hn : 2≤n) (i : Fin n) (hiX : i∈X) :
    configurationY (G := G) X=configurationY (G := G) (X\{i})+jointDelta G n := by
  have h := joint_deletion_identity i hiX (joint_not_coloop_nontrivial (G := G) X i hiX hn)
  rw [joint_correction_sum_nontrivial_choose i hiX] at h
  rw [h,jointDelta]
  ring

end Dowling
