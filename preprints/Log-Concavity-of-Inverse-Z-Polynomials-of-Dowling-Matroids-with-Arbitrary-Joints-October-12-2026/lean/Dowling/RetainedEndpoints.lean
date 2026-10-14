import Dowling.FullEndpoints
import Dowling.RetainedNontrivialIdentity
import Dowling.RetainedTrivialIdentity

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem jointRankCorrection_constant (r : ℕ) : (jointRankCorrection G n r).coeff 0=0 := by
  unfold jointRankCorrection
  split_ifs with h
  · rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
    rw [ite_eq_right (by omega),mul_zero]
  · simp

theorem jointDelta_constant : (jointDelta G n).coeff 0=(fullY G (n-1)).coeff 0 := by
  simp [jointDelta,coeff_sub,Polynomial.finsetSum_coeff,jointRankCorrection_constant,
    add_mul,coeff_add]

theorem missingJointCorrection_constant (ell : ℕ) : (missingJointCorrection G n ell).coeff 0=0 := by
  simp [missingJointCorrection,Polynomial.finsetSum_coeff,jointRankCorrection_constant]

/-- A common endpoint formula, retaining the exact number of actual joints. -/
theorem retained_constant_difference (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) :
    (configurationY (G := G) X).coeff 0=(fullY G n).coeff 0-
      ((n-X.toFinset.card : ℕ) : ℤ)*(fullY G (n-1)).coeff 0 := by
  rcases subsingleton_or_nontrivial G with hG | hG
  · have hx : X.Nonempty := hX.resolve_left (fun h => not_nontrivial G h)
    rw [retained_trivial_identity X hx,coeff_sub,coeff_sub,coeff_C_mul,
      jointDelta_constant,missingJointCorrection_constant,sub_zero]
  · rw [retained_nontrivial_identity hn X,coeff_sub,coeff_C_mul,jointDelta_constant]

theorem retained_constant_product (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) :
    (configurationY (G := G) X).coeff 0=
      (((Fintype.card G : ℤ)-1)*(n-1 : ℕ)+X.toFinset.card)*
        ∏ j∈range (n-1),((Fintype.card G : ℤ)*j+1) := by
  rw [retained_constant_difference hn X hX]
  have he : n-1+1=n := by omega
  have hs := fullY_constant_succ (G := G) (n-1)
  rw [he] at hs
  rw [hs,fullY_constant_product]
  have hk : X.toFinset.card≤n := by simpa using Finset.card_le_univ X.toFinset
  rw [Nat.cast_sub hk,Nat.cast_sub (by omega : 1≤n)]
  push_cast
  ring

end Dowling
