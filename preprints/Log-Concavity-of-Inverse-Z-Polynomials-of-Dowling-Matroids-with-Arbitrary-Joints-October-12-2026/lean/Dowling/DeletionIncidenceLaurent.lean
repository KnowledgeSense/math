import BoseBurton.ZIncidenceConvolution
import Mathlib.Algebra.Polynomial.Laurent

/-! Laurent algebra for the genuine deletion intertwiner. The polynomial-support
condition is explicit; involution-fixed Laurent vectors alone do not have the
finite integer basis claimed without that condition in arXiv:2510.01086v1 §3.1.
The corrected condition is Braden–Vysogorets, arXiv:1909.09888, §2.5. -/
noncomputable section
namespace Dowling
open scoped LaurentPolynomial
open LaurentPolynomial

abbrev DeletionLaurent := LaurentPolynomial ℤ

/-- The literal substitution x ↦ t⁻², without a square-root choice. -/
def deletionSubst : Polynomial ℤ→+*DeletionLaurent :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (T (-2))

/-- The rank-normalized KL basis coefficient. -/
def deletionLift (d : ℤ) (p : Polynomial ℤ) : DeletionLaurent := T d*deletionSubst p

 theorem deletionSubst_C (a : ℤ) : deletionSubst (Polynomial.C a)=C a := by
  simp [deletionSubst]

 theorem deletionSubst_X : deletionSubst Polynomial.X=T (-2) := by
  simp [deletionSubst]

 theorem deletionSubst_monomial (k : ℕ) (a : ℤ) :
    deletionSubst (Polynomial.monomial k a)=C a*T (-2*(k : ℤ)) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,deletionSubst_C,deletionSubst_X,T_pow]
  congr 2
  omega

 theorem deletionLift_monomial (d : ℤ) (k : ℕ) (a : ℤ) :
    deletionLift d (Polynomial.monomial k a)=C a*T (d-2*k) := by
  rw [deletionLift,deletionSubst_monomial]
  rw [show d-2*(k : ℤ)=d+(-2*(k : ℤ)) by ring,T_add]
  ring

 theorem deletionLift_add (d : ℤ) (p q : Polynomial ℤ) :
    deletionLift d (p+q)=deletionLift d p+deletionLift d q := by
  simp [deletionLift,mul_add]

 theorem deletionLift_mul (d e : ℤ) (p q : Polynomial ℤ) :
    deletionLift (d+e) (p*q)=deletionLift d p*deletionLift e q := by
  simp only [deletionLift,map_mul,T_add]
  ring

 theorem deletionLaurent_monomial_coeff (a d j : ℤ) :
    (C a*T d : DeletionLaurent).coeff j=if d=j then a else 0 := by
  rw [← single_eq_C_mul_T]
  change (Finsupp.single d a) j = _
  exact Finsupp.single_apply

 theorem deletionPolynomial_coeff_nat (p : Polynomial ℤ) (n : ℕ) :
    p.toLaurent.coeff n=p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial k a =>
    rw [Polynomial.toLaurent_C_mul_T,deletionLaurent_monomial_coeff,Polynomial.coeff_monomial]
    simp only [Nat.cast_inj]

 theorem deletionPolynomial_coeff_neg (p : Polynomial ℤ) (j : ℤ) (hj : j<0) :
    p.toLaurent.coeff j=0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hq,add_zero]
  | monomial k a =>
    rw [Polynomial.toLaurent_C_mul_T,deletionLaurent_monomial_coeff,ite_eq_right (by omega)]

/-- A polynomial fixed by Laurent inversion is genuinely constant. -/
theorem deletionPolynomial_invert_constant (p : Polynomial ℤ)
    (hp : LaurentPolynomial.invert p.toLaurent=p.toLaurent) : p=Polynomial.C (p.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have h := congrArg (fun f : DeletionLaurent=>f.coeff (n+1 : ℕ)) hp
    rw [invert_apply,deletionPolynomial_coeff_nat,deletionPolynomial_coeff_neg _ _ (by omega)] at h
    rw [Polynomial.coeff_C,ite_eq_right (by omega)]
    exact h.symm

end Dowling
