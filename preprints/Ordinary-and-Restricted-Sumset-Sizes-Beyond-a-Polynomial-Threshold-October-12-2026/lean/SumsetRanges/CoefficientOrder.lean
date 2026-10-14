import SumsetRanges.RelationSteps

open Finset Polynomial
namespace SumsetRanges

def CoeffNonneg (P : Polynomial ℤ) : Prop := ∀ q, 0 ≤ P.coeff q
def CoeffLE (P Q : Polynomial ℤ) : Prop := ∀ q, P.coeff q ≤ Q.coeff q

theorem coeffNonneg_one : CoeffNonneg 1 := by
  intro q
  simp only [coeff_one]
  split <;> norm_num

theorem coeffNonneg_X_pow (r : ℕ) : CoeffNonneg (X^r) := by
  intro q
  simp only [coeff_X_pow]
  split <;> norm_num

theorem coeffNonneg_natCast (n : ℕ) : CoeffNonneg (n : Polynomial ℤ) := by
  intro q
  simp only [coeff_natCast_ite]
  split <;> positivity

theorem coeffNonneg_add {P Q : Polynomial ℤ} (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) :
    CoeffNonneg (P+Q) := by
  intro q
  rw [coeff_add]
  exact add_nonneg (hP q) (hQ q)

theorem coeffNonneg_mul {P Q : Polynomial ℤ} (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) :
    CoeffNonneg (P*Q) := by
  intro q
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (hP p.1) (hQ p.2))

theorem coeffNonneg_pow {P : Polynomial ℤ} (hP : CoeffNonneg P) (r : ℕ) :
    CoeffNonneg (P^r) := by
  induction r with
  | zero => simpa using coeffNonneg_one
  | succ r ih => rw [pow_succ]; exact coeffNonneg_mul ih hP

theorem coeffNonneg_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ)
    (hf : ∀ i∈s,CoeffNonneg (f i)) : CoeffNonneg (∑ i∈s,f i) := by
  intro q
  rw [finsetSum_coeff]
  exact Finset.sum_nonneg (fun i hi => hf i hi q)

theorem coeffNonneg_restrictedPolynomial {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : CoeffNonneg (restrictedPolynomial A) := by
  intro q
  rw [coeff_restrictedPolynomial]
  positivity

theorem coeffNonneg_rowPolynomial (m : ℕ) : CoeffNonneg (rowPolynomial m) := by
  intro q
  rw [coeff_rowPolynomial]
  positivity

theorem coeffLE_mul {P Q R S : Polynomial ℤ} (hP : CoeffNonneg P) (hS : CoeffNonneg S)
    (hPQ : CoeffLE P Q) (hRS : CoeffLE R S) : CoeffLE (P*R) (Q*S) := by
  intro q
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_le_sum
  intro p _
  calc
    P.coeff p.1 * R.coeff p.2 ≤ P.coeff p.1*S.coeff p.2 := mul_le_mul_of_nonneg_left (hRS p.2) (hP p.1)
    _ ≤ Q.coeff p.1*S.coeff p.2 := mul_le_mul_of_nonneg_right (hPQ p.1) (hS p.2)

theorem shared_step_term_nonneg (m u j : ℕ) : CoeffNonneg
    ((u.choose j : Polynomial ℤ)*(rowPolynomial m)^(u-j)*
      X^(m+j-1)*(∑ l∈range j,X^(l*(m-2)))) := by
  apply coeffNonneg_mul
  · exact coeffNonneg_mul (coeffNonneg_mul (coeffNonneg_natCast _) (coeffNonneg_pow (coeffNonneg_rowPolynomial m) _))
      (coeffNonneg_X_pow _)
  · exact coeffNonneg_sum _ _ (fun l _ => coeffNonneg_X_pow _)

theorem sharedBlock_step_nonneg (m u : ℕ) (hm : 2 ≤ m) :
    CoeffNonneg ((1+X)^m*sharedBlockPolynomial m u-sharedBlockPolynomial m (u+1)) := by
  rw [sharedBlock_step m u hm]
  exact coeffNonneg_sum _ _ (fun j _ => shared_step_term_nonneg m u j)

theorem sharedBlock_step_lower (m u : ℕ) (hm : 2 ≤ m) (hu : 1 ≤ u) :
    CoeffLE ((u : Polynomial ℤ)*X^m*(rowPolynomial m)^(u-1))
      ((1+X)^m*sharedBlockPolynomial m u-sharedBlockPolynomial m (u+1)) := by
  intro q
  rw [sharedBlock_step m u hm,finsetSum_coeff]
  have hh := Finset.single_le_sum (s := range (u+1))
    (f := fun j => (((u.choose j : Polynomial ℤ)*(rowPolynomial m)^(u-j)*
      X^(m+j-1)*(∑ l∈range j,X^(l*(m-2)))).coeff q))
    (fun j _ => shared_step_term_nonneg m u j q) (a := 1) (mem_range.mpr (by omega))
  have he : (u.choose 1 : Polynomial ℤ)*(rowPolynomial m)^(u-1)*
      X^(m+1-1)*(∑ l∈range 1,X^(l*(m-2))) = (u : Polynomial ℤ)*X^m*(rowPolynomial m)^(u-1) := by
    simp
    ring
  rw [he] at hh
  exact hh

end SumsetRanges
