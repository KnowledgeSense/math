import Dowling.DeletionKLBottom

noncomputable section
namespace Dowling
open Finset LaurentPolynomial MatroidInverseZ
open scoped Classical

 theorem deletionLift_injective (d : ℤ) : Function.Injective (deletionLift d) := by
  intro p q h
  apply deletionSubst_injective
  have ht := congrArg (fun z : DeletionLaurent=>T (-d)*z) h
  simp only [deletionLift,← mul_assoc,← T_add,neg_add_cancel,T_zero,one_mul] at ht
  exact ht

 theorem deletion_neg_one_sub_even (n k : ℕ) (hkn : k≤n) (hk : k%2=0) :
    (-1 : ℤ)^(n-k)=(-1)^n := by
  have hp : (-1 : ℤ)^k=1 := by
    rw [show k=2*(k/2) by omega,pow_mul]
    norm_num
  have h := pow_add (-1 : ℤ) (n-k) k
  rw [Nat.sub_add_cancel hkn,hp,mul_one] at h
  exact h.symm

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]

 theorem deletionYCoordinate_even (r : α→ℕ) (hr : Monotone r) (t b : α)
    (hbt : b≤t) (hb : r b%2=0) :
    deletionYCoordinate r t b=deletionLift (2*(r t : ℤ))
      (Polynomial.C ((-1 : ℤ)^r t)*(Polynomial.X^(r b/2)*inverseZ r b t)) := by
  rw [deletionYCoordinate,signedInverseZKernel_apply r hr]
  rw [deletion_neg_one_sub_even (r t) (r b) (hr hbt) hb]
  simp only [deletionLift,map_mul,deletionSubst_C,map_pow,deletionSubst_X,T_pow]
  have ht : (T (2*(r t : ℤ)-r b) : DeletionLaurent)=T (2*(r t : ℤ))*T ((r b/2 : ℕ)*(-2 : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  rw [ht]
  ring

 theorem deletionYCoordinate_bottom (r : α→ℕ) (hr : Monotone r) (t b : α)
    (hbt : b≤t) (hb : r b=0) :
    deletionYCoordinate r t b=deletionLift (2*(r t : ℤ))
      (Polynomial.C ((-1 : ℤ)^r t)*inverseZ r b t) := by
  rw [deletionYCoordinate_even r hr t b hbt (by rw [hb])]
  simp only [hb,Nat.zero_div,pow_zero,one_mul]

 theorem deletionYCoordinate_atom (r : α→ℕ) (hr : Monotone r) (t e : α)
    (het : e≤t) (he : r e=1) :
    (T 1+T (-1))*deletionYCoordinate r t e=
      -deletionLift (2*(r t : ℤ))
        (Polynomial.C ((-1 : ℤ)^r t)*((1+Polynomial.X)*inverseZ r e t)) := by
  have hn : 1≤r t := by have := hr het; omega
  have hsign : (-1 : ℤ)^(r t-1)= -((-1 : ℤ)^r t) := by
    have h := pow_add (-1 : ℤ) (r t-1) 1
    rw [Nat.sub_add_cancel hn,pow_one,mul_neg_one] at h
    omega
  rw [deletionYCoordinate,signedInverseZKernel_apply r hr,he,hsign]
  simp only [deletionLift,map_mul,map_add,map_one,deletionSubst_C,deletionSubst_X,map_neg]
  have ht1 : (T 1 : DeletionLaurent)*T (2*(r t : ℤ)-1)=T (2*(r t : ℤ)) := by rw [← T_add]; congr 1; ring
  have ht2 : (T (-1) : DeletionLaurent)*T (2*(r t : ℤ)-1)=T (2*(r t : ℤ))*T (-2) := by
    rw [← T_add,← T_add]; congr 1; ring
  calc
    _ = -(T 1*T (2*(r t : ℤ)-1)+T (-1)*T (2*(r t : ℤ)-1))*
        C ((-1 : ℤ)^r t)*deletionSubst (inverseZ r e t) := by ring
    _ = _ := by rw [ht1,ht2]; ring

end Dowling
