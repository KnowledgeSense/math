import Dowling.DeletionKLTau

noncomputable section
namespace Dowling
open Finset LaurentPolynomial
open scoped Classical
variable {α : Type*} [Fintype α] [PartialOrder α] [LocallyFiniteOrder α]

/-- Laurent linear combinations of the actual triangular KL basis. -/
def deletionKLCombination (r : α→ℕ) (c : α→DeletionLaurent) (a : α) : DeletionLaurent :=
  ∑ b,deletionKLVector r b a*c b

 theorem deletionKLCombination_injective (r : α→ℕ) : Function.Injective (deletionKLCombination r) := by
  intro v w h
  funext a
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    have he : (∑ b,deletionKLVector r b a*(v b-w b))=0 := by
      simp only [mul_sub,sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun h a)
    rw [sum_eq_single a] at he
    · simpa only [deletionKLVector_self,one_mul,sub_eq_zero] using he
    · intro b hb hba
      by_cases hab : a≤b
      · rw [ih b (lt_of_le_of_ne hab (Ne.symm hba)),sub_self,mul_zero]
      · simp [deletionKLVector,hab]
    · simp

variable {β : Type*} [Fintype β] [PartialOrder β]

 omit [PartialOrder α] [LocallyFiniteOrder α] [Fintype β] [PartialOrder β] in
 theorem deletionPush_sum {ι : Type*} (r : α→ℕ) (s : β→ℕ) (d : α→β)
    (q : Finset ι) (v : ι→α→DeletionLaurent) (x : β) :
    deletionPush r s d (fun a=>∑ i∈q,v i a) x=∑ i∈q,deletionPush r s d (v i) x := by
  simp only [deletionPush,mul_sum,ite_sum_zero]
  rw [sum_comm]

 omit [PartialOrder α] [LocallyFiniteOrder α] [Fintype β] [PartialOrder β] in
 theorem deletionPush_mul_right (r : α→ℕ) (s : β→ℕ) (d : α→β)
    (v : α→DeletionLaurent) (z : DeletionLaurent) (x : β) :
    deletionPush r s d (fun a=>v a*z) x=deletionPush r s d v x*z := by
  simp only [deletionPush,sum_mul]
  apply sum_congr rfl
  intro a ha
  by_cases hax : d a=x
  · simp only [hax,ite_true,mul_assoc]
  · simp only [hax,ite_false,zero_mul]

end Dowling
