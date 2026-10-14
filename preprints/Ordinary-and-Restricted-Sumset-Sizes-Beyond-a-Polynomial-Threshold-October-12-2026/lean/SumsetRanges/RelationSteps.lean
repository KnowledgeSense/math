import SumsetRanges.LinearBlockSeries

open Finset Polynomial
namespace SumsetRanges

theorem linearBlock_step (m r : ℕ) (hm : 2 ≤ m) :
    (1+X)^(2*m)*restrictedPolynomial (linearBlocks m r) -
      restrictedPolynomial (linearBlocks m (r+1)) =
      X^m*restrictedPolynomial (linearBlocks m r) := by
  rw [restrictedPolynomial_linearBlocks m r hm,restrictedPolynomial_linearBlocks m (r+1) hm]
  rw [pow_succ]
  ring

theorem ambiguityPolynomial_succ (m j : ℕ) (hm : 2 ≤ m) :
    ambiguityPolynomial m (j+1) = X*ambiguityPolynomial m j + X^((j+1)*(m-1)) := by
  unfold ambiguityPolynomial
  rw [Finset.sum_range_succ,Finset.mul_sum]
  have he : j+1+(j+1)*(m-2)=(j+1)*(m-1) := by
    have hm' : m-1=(m-2)+1 := by omega
    rw [hm']
    ring
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [← pow_succ']
  congr 1
  omega

theorem ambiguityPolynomial_difference (m j : ℕ) (hm : 2 ≤ m) :
    (X+X^(m-1))*ambiguityPolynomial m j - ambiguityPolynomial m (j+1) =
      X^(m+j-1)*(∑ l ∈ range j, X^(l*(m-2))) := by
  rw [ambiguityPolynomial_succ m j hm]
  have he : X^(m-1)*ambiguityPolynomial m j =
      X^(m+j-1)*(∑ l ∈ range j, X^(l*(m-2))) + X^((j+1)*(m-1)) := by
    unfold ambiguityPolynomial
    rw [Finset.sum_range_succ,mul_add,Finset.mul_sum,Finset.mul_sum]
    have hm' : m-1=(m-2)+1 := by omega
    have hlast : (X : Polynomial ℤ)^(m-1)*X^(j+j*(m-2)) = X^((j+1)*(m-1)) := by
      rw [← pow_add]
      congr 1
      rw [hm']
      ring
    rw [hlast]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [← pow_add,← pow_add]
    congr 1
    omega
  rw [add_mul,he]
  ring

/-- Binomial transform used to enumerate the shared relation blocks. -/
noncomputable def binomialTransform {R : Type*} [CommRing R] (x : R) (f : ℕ → R) (u : ℕ) : R :=
  ∑ j ∈ range (u+1), (u.choose j : R)*x^(u-j)*f j

theorem binomialTransform_succ {R : Type*} [CommRing R] (x : R) (f : ℕ → R) (u : ℕ) :
    binomialTransform x f (u+1) = x*binomialTransform x f u +
      binomialTransform x (fun j => f (j+1)) u := by
  unfold binomialTransform
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  have hext : (∑ j ∈ range (u+1), (u.choose j : R)*x^(u-j)*f j) =
      ∑ j ∈ range (u+2), (u.choose j : R)*x^(u-j)*f j := by
    conv_rhs => rw [show u+2=(u+1)+1 by omega,Finset.sum_range_succ]
    simp
  conv_rhs => lhs; arg 2; rw [hext, show u+2=(u+1)+1 by omega, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  rw [mul_add,Finset.mul_sum]
  have hterm : ∀ j ∈ range (u+1),
      ((u+1).choose (j+1) : R)*x^(u-j)*f (j+1) =
        x*((u.choose (j+1) : R)*x^(u-(j+1))*f (j+1)) +
        (u.choose j : R)*x^(u-j)*f (j+1) := by
    intro j hj
    rw [Nat.choose_succ_succ,Nat.cast_add]
    by_cases hj' : j<u
    · have he : u-j=u-(j+1)+1 := by omega
      rw [he,pow_succ]
      ring
    · have hju : j=u := by have := mem_range.mp hj; omega
      subst j
      simp
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib] at hsum
  rw [hsum]
  rw [pow_succ]
  ring

theorem sharedBlockPolynomial_transform (m u : ℕ) (hm : 2 ≤ m) :
    sharedBlockPolynomial m u = binomialTransform (rowPolynomial m) (ambiguityPolynomial m) u := by
  rw [sharedBlockPolynomial_formula m u hm]
  unfold binomialTransform
  rw [rowPolynomial_eq m hm]

theorem sharedBlock_step (m u : ℕ) (hm : 2 ≤ m) :
    (1+X)^m*sharedBlockPolynomial m u - sharedBlockPolynomial m (u+1) =
      ∑ j ∈ range (u+1), (u.choose j : Polynomial ℤ)*(rowPolynomial m)^(u-j) *
        X^(m+j-1)*(∑ l ∈ range j, X^(l*(m-2))) := by
  rw [sharedBlockPolynomial_transform m u hm,sharedBlockPolynomial_transform m (u+1) hm,
    binomialTransform_succ]
  unfold binomialTransform
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he := ambiguityPolynomial_difference m j hm
  have hphi := rowPolynomial_eq m hm
  calc
    _ = (u.choose j : Polynomial ℤ)*(rowPolynomial m)^(u-j) *
      ((X+X^(m-1))*ambiguityPolynomial m j-ambiguityPolynomial m (j+1)) := by
        rw [hphi]
        ring
    _ = _ := by rw [he]; ring

end SumsetRanges
