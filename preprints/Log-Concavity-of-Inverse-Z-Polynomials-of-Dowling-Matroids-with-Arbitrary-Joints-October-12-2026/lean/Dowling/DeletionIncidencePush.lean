import Dowling.DeletionKLBasisExpansion

noncomputable section
namespace Dowling
open Finset LaurentPolynomial
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]

/-- Literal rank-shifted sum over each fiber of the deletion map. -/
def deletionPush (r : α→ℕ) (s : β→ℕ) (d : α→β) (v : α→DeletionLaurent)
    (b : β) : DeletionLaurent :=
  ∑ a,if d a=b then T ((s b : ℤ)-r a)*v a else 0

theorem deletionPush_rankSum (r : α→ℕ) (s : β→ℕ) (d : α→β) (c : β→α)
    (hgc : ∀ b a,c b≤a↔b≤d a) (hr : ∀ b,r (c b)=s b)
    (v : α→DeletionLaurent) (b : β) :
    deletionRankSum s (deletionPush r s d v) b=deletionRankSum r v (c b) := by
  unfold deletionRankSum deletionPush
  simp only [sum_filter,mul_sum,mul_ite,mul_zero,ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [sum_eq_single (d a)]
  · by_cases hba : b≤d a
    · rw [ite_eq_left hba,ite_eq_left rfl,ite_eq_left ((hgc b a).mpr hba)]
      rw [← mul_assoc,← T_add,hr]
      congr 2
      ring
    · rw [ite_eq_right hba,ite_eq_right (fun h=>hba ((hgc b a).mp h))]
  · intro j hj hja
    by_cases hbj : b≤j
    · rw [ite_eq_left hbj,ite_eq_right (Ne.symm hja)]
    · rw [ite_eq_right hbj]
  · simp

theorem deletionPush_palindromic (r : α→ℕ) (s : β→ℕ) (d : α→β) (c : β→α)
    (hgc : ∀ b a,c b≤a↔b≤d a) (hr : ∀ b,r (c b)=s b)
    {v : α→DeletionLaurent} (hv : DeletionPerverse r v) (b : β) :
    invert (deletionRankSum s (deletionPush r s d v) b)=
      deletionRankSum s (deletionPush r s d v) b := by
  rw [deletionPush_rankSum r s d c hgc hr]
  exact hv.palindromic (c b)

end Dowling
