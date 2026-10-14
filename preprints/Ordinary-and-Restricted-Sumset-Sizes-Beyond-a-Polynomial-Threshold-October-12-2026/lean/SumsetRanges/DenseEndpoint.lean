import SumsetRanges.SparseBaseline
import SumsetRanges.DenseConvolutionBounds

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

theorem dense_endpoint_coeff (h n q : ℕ) (hn : 1≤n) (hq : q≤h) :
    (restrictedPolynomial (denseSet n (h*(n-1)+1))).coeff q=
      ((1+X)*restrictedPolynomial (range n)).coeff q := by
  cases q with
  | zero => simp [Polynomial.mul_coeff_zero,restrictedPolynomial_constant]
  | succ q =>
    rw [coeff_restrictedPolynomial,dense_restricted_endpoint h n q hn hq]
    rw [add_mul,one_mul,coeff_add,coeff_X_mul,coeff_restrictedPolynomial,coeff_restrictedPolynomial]
    push_cast
    rfl

theorem coeff_mul_congr_upto (P Q R : Polynomial ℤ) (h : ℕ)
    (he : ∀q≤h,Q.coeff q=R.coeff q) : (P*Q).coeff h=(P*R).coeff h := by
  rw [coeff_mul_range_reversed,coeff_mul_range_reversed]
  apply Finset.sum_congr rfl
  intro q hq
  rw [he q (by have := mem_range.mp hq; omega)]

theorem dense_endpoint_product (h c n : ℕ) (hn : 1≤n) :
    ((1+X)^c*restrictedPolynomial (denseSet n (h*(n-1)+1))).coeff h=
      ((1+X)^(c+1)*restrictedPolynomial (range n)).coeff h := by
  calc
    _=((1+X)^c*((1+X)*restrictedPolynomial (range n))).coeff h :=
      coeff_mul_congr_upto _ _ _ h (fun q hq => dense_endpoint_coeff h n q hn hq)
    _=_ := by rw [← mul_assoc,← pow_succ]

@[simp] theorem denseSet_at_minimum (n : ℕ) : denseSet n n=range (n+1) := by
  exact (Finset.range_add_one (n := n)).symm

theorem restrictedPolynomial_pair : restrictedPolynomial (range 2)=(1+X)^2 := by
  ext q
  rw [coeff_restrictedPolynomial,coeff_one_add_X_pow]
  cases q with
  | zero => simp
  | succ q =>
    cases q with
    | zero => simp
    | succ q =>
      cases q with
      | zero => decide
      | succ q =>
        have hz := card_restrictedSums_le (range 2) (q+3)
        simp only [card_range] at hz
        rw [Nat.choose_eq_zero_of_lt (by omega)] at hz
        have he : (restrictedSums (range 2) (q+3)).card=0 := by omega
        rw [he,Nat.choose_eq_zero_of_lt (by omega)]

end SumsetRanges
