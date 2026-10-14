import Dowling.DeletionKLPush

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ
open scoped Classical

 theorem deletionT_mul_coeff (d j : ℤ) (v : DeletionLaurent) :
    (T d*v).coeff j=v.coeff (j-d) := by
  simp only [T,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1
  omega

 theorem deletionLift_coeff_one (n : ℕ) (p : Polynomial ℤ) :
    (deletionLift n p).coeff 1=if n%2=1 then p.coeff (n/2) else 0 := by
  rw [deletionLift_coeff]
  by_cases hn : n%2=1
  · rw [ite_eq_left hn,sum_eq_single (n/2)]
    · rw [ite_eq_left (by omega)]
    · intro k hk hkn
      rw [ite_eq_right (by omega)]
    · intro hnot
      rw [Polynomial.notMem_support_iff.mp hnot]
      simp
  · rw [ite_eq_right hn]
    apply sum_eq_zero
    intro k hk
    rw [ite_eq_right (by omega)]

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]

/-- The actual top KL coefficient, zero in even interval rank. -/
def deletionTau (r : α→ℕ) (a b : α) : ℤ :=
  if a≤b ∧ (r b-r a)%2=1 then (kl r b a).coeff ((r b-r a)/2) else 0

 theorem deletionKLVector_coeff_one (r : α→ℕ) (hr : Monotone r) (a b : α) :
    (deletionKLVector r b a).coeff 1=deletionTau r a b := by
  by_cases hab : a≤b
  · rw [deletionKLVector,ite_eq_left hab]
    have hd : ((r b-r a : ℕ) : ℤ)=(r b : ℤ)-r a := by have := hr hab; omega
    rw [← hd,deletionLift_coeff_one]
    simp only [deletionTau,hab,true_and]
  · simp [deletionKLVector,deletionTau,hab]

variable {β : Type*} [Fintype α] [Fintype β] [PartialOrder β]

 omit [Fintype β] [PartialOrder β] in
 theorem deletionKL_push_constantCoeff (r : α→ℕ) (s : β→ℕ) (d : α→β)
    (hr : Monotone r) (hle : ∀ a,s (d a)≤r a) (hdrop : ∀ a,r a≤s (d a)+1)
    (b : α) (x : β) :
    (deletionPush r s d (deletionKLVector r b) x).coeff 0=
      ∑ a,if d a=x then
        if r a=s (d a) then (if a=b then 1 else 0) else deletionTau r a b
      else 0 := by
  rw [deletionPush,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply sum_congr rfl
  intro a ha
  by_cases hax : d a=x
  · rw [ite_eq_left hax,ite_eq_left hax,deletionT_mul_coeff]
    by_cases he : r a=s (d a)
    · rw [ite_eq_left he]
      have hz : (0 : ℤ)-((s x : ℤ)-r a)=0 := by rw [← hax,he]; omega
      rw [hz,deletionKLVector_constantCoeff]
    · rw [ite_eq_right he]
      have h1 : (0 : ℤ)-((s x : ℤ)-r a)=1 := by
        have := hle a
        have := hdrop a
        rw [hax] at *
        omega
      rw [h1,deletionKLVector_coeff_one r hr]
  · simp [hax]

end Dowling
