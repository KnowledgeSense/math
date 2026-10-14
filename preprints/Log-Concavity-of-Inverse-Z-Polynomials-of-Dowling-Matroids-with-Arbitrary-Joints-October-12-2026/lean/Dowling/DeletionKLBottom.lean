import Dowling.DeletionKLTransition

noncomputable section
namespace Dowling
open Finset LaurentPolynomial
open scoped Classical
variable {α β : Type*} [Fintype α] [Fintype β] [PartialOrder α] [PartialOrder β]
  [LocallyFiniteOrder α] [LocallyFiniteOrder β]

 omit [Fintype β] [PartialOrder β] [LocallyFiniteOrder β] in
 theorem deletionKLTransition_bottom (r : α→ℕ) (s : β→ℕ) (d : α→β)
    (hr : Monotone r) (hle : ∀ a,s (d a)≤r a) (hdrop : ∀ a,r a≤s (d a)+1)
    (a e : α) (x : β) (ha : r a=0) (he : r e=1) (hx : s x=0)
    (hf : ∀ b,d b=x↔b=a∨b=e) (b : α) :
    deletionKLTransition r s d b x=
      (if b=a then 1 else 0)+(if b=e then T 1+T (-1) else 0)+
        (if s (d b)=r b then C (deletionTau r e b) else 0) := by
  have hae : a≠e := by intro h; rw [h,he] at ha; omega
  have hda : d a=x := (hf a).mpr (Or.inl rfl)
  have hde : d e=x := (hf e).mpr (Or.inr rfl)
  have hsda : s (d a)=r a := by rw [hda,hx,ha]
  by_cases hb : s (d b)=r b
  · have hbe : b≠e := by intro h; subst b; rw [hde,hx,he] at hb; omega
    rw [deletionKLTransition,ite_eq_left hb,ite_eq_right hbe,ite_eq_left hb,
      deletionKL_push_constantCoeff r s d hr hle hdrop,
      deletion_two_fiber_sum d x a e hae hf]
    simp only [hsda,ite_true,hde,hx,he,show ¬(1:ℕ)=0 by omega,ite_false,map_add,
      add_zero]
    by_cases hba : b=a
    · subst b
      simp
    · simp [hba,Ne.symm hba]
  · have hba : b≠a := by intro h; subst b; exact hb hsda
    rw [deletionKLTransition,ite_eq_right hb,ite_eq_right hba,ite_eq_right hb,zero_add,add_zero]
    have hdb : d b=x↔b=e := by rw [hf]; simp [hba]
    rw [hdb]

 omit [Fintype β] [PartialOrder β] [LocallyFiniteOrder β] in
 theorem deletionKLTransition_bottom_sum (r : α→ℕ) (s : β→ℕ) (d : α→β)
    (hr : Monotone r) (hle : ∀ a,s (d a)≤r a) (hdrop : ∀ a,r a≤s (d a)+1)
    (a e : α) (x : β) (ha : r a=0) (he : r e=1) (hx : s x=0)
    (hf : ∀ b,d b=x↔b=a∨b=e) (v : α→DeletionLaurent) :
    (∑ b,deletionKLTransition r s d b x*v b)=v a+(T 1+T (-1))*v e+
      ∑ b,if s (d b)=r b then C (deletionTau r e b)*v b else 0 := by
  simp_rw [deletionKLTransition_bottom r s d hr hle hdrop a e x ha he hx hf]
  simp only [add_mul,sum_add_distrib,ite_mul,one_mul,zero_mul]
  simp

end Dowling
