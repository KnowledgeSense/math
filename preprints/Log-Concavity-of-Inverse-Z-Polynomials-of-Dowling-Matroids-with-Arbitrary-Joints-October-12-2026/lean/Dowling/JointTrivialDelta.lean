import Dowling.JointCorrectionSumTrivial

noncomputable section
namespace Dowling
open Finset Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] [Subsingleton G] {n : ℕ} {X : Set (Fin n)}

/-- The missing-mark correction, still in genuine full-Dowling invariants. -/
def missingJointCorrection (G : Type*) [Group G] [Fintype G] (n ell : ℕ) : Polynomial ℤ :=
  ∑ r∈range (n+1),C ((ell.choose r : ℕ) : ℤ)*jointRankCorrection G n r

def missingJointIncrement (G : Type*) [Group G] [Fintype G] (n ell : ℕ) : Polynomial ℤ :=
  ∑ r∈range (n+1),C ((ell.choose (r-1) : ℕ) : ℤ)*jointRankCorrection G n r

theorem joint_correction_sum_trivial_difference (i : Fin n) (hiX : i∈X) :
    (∑ p : Configuration G X,if IsJointCorrection X i p.val then jointCorrectionTerm i hiX p else 0)=
      (∑ r∈range (n+1),C (((n-1).choose (r-1) : ℕ) : ℤ)*jointRankCorrection G n r)-
        missingJointIncrement G n (n-X.toFinset.card) := by
  rw [joint_correction_sum_trivial i hiX,missingJointIncrement,← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro r hr
  by_cases hz : r=0
  · simp [hz,jointRankCorrection]
  · have hcard := markedJointZeroSets_card X i hiX r (by omega)
    have hle : (n-X.toFinset.card).choose (r-1)≤(n-1).choose (r-1) := by
      have hh := card_filter_add_card_filter_not (s := jointZeroSets i r)
        (fun Z : Finset (Fin n) => ∃ j∈X,j≠i ∧ j∈Z)
      rw [jointZeroSets_card i r (by omega),jointZeroSets_unmarked_card X i hiX r (by omega)] at hh
      omega
    rw [hcard]
    rw [← map_natCast C, Nat.cast_sub hle,map_sub,sub_mul]

theorem joint_deletion_trivial (i : Fin n) (hiX : i∈X) (hj : ∃ j∈X,j≠i) :
    configurationY (G := G) X=configurationY (G := G) (X\{i})+jointDelta G n+
      missingJointIncrement G n (n-X.toFinset.card) := by
  have h := joint_deletion_identity i hiX (joint_not_coloop_other_mark (G := G) X i hiX hj)
  rw [joint_correction_sum_trivial_difference i hiX] at h
  rw [h,jointDelta]
  ring

omit [Subsingleton G] in
/-- The positive-rank correction has no rank-zero summand. -/
theorem missingJointCorrection_zero : missingJointCorrection G n 0=0 := by
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hz : r=0
  · simp [hz,jointRankCorrection]
  · simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hz)]

omit [Subsingleton G] in
theorem missingJointCorrection_succ (ell : ℕ) :
    missingJointCorrection G n (ell+1)=missingJointCorrection G n ell+missingJointIncrement G n ell := by
  rw [missingJointCorrection,missingJointCorrection,missingJointIncrement,← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  cases r with
  | zero => simp [jointRankCorrection]
  | succ r =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.succ_sub_one,Nat.cast_add,map_add,add_mul]
    ring

end Dowling
