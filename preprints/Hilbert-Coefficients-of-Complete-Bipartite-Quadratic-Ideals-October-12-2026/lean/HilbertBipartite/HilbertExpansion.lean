import HilbertBipartite.CoefficientConvolution
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support

open Finset Polynomial
namespace HilbertBipartite

/-- The coefficient of z^r in P(z)/(1-z)^(n+1), as a finite convolution. -/
noncomputable def hilbertConvolution (P : Polynomial ℚ) (n r : ℕ) : ℚ :=
  ∑ j ∈ range (r+1), P.coeff j * ((r-j+n).choose n : ℚ)

theorem hilbertConvolution_add (P Q : Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution (P+Q) n r = hilbertConvolution P n r + hilbertConvolution Q n r := by
  simp [hilbertConvolution, add_mul, sum_add_distrib]

theorem hilbertConvolution_sub (P Q : Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution (P-Q) n r = hilbertConvolution P n r - hilbertConvolution Q n r := by
  simp [hilbertConvolution, sub_mul, sum_sub_distrib]

theorem hilbertConvolution_C_mul (a : ℚ) (P : Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution (C a*P) n r = a * hilbertConvolution P n r := by
  simp [hilbertConvolution, mul_assoc, mul_sum]

@[simp] theorem hilbertConvolution_one (n r : ℕ) :
    hilbertConvolution 1 n r = ((r+n).choose n : ℚ) := by
  simp [hilbertConvolution, Polynomial.coeff_one, Finset.sum_ite_eq']

@[simp] theorem hilbertConvolution_zero_degree (P : Polynomial ℚ) (n : ℕ) :
    hilbertConvolution P n 0 = P.coeff 0 := by simp [hilbertConvolution]

theorem hilbertConvolution_X_mul_succ (P : Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution (X*P) n (r+1) = hilbertConvolution P n r := by
  unfold hilbertConvolution
  rw [Finset.sum_range_succ']
  simp only [coeff_X_mul_zero, zero_mul, add_zero, coeff_X_mul, Nat.add_sub_add_right]

theorem hilbertConvolution_pascal (P : Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution P (n+1) (r+1) - hilbertConvolution P (n+1) r =
      hilbertConvolution P n (r+1) := by
  unfold hilbertConvolution
  conv_lhs => lhs; rw [Finset.sum_range_succ]
  conv_rhs => rw [Finset.sum_range_succ]
  have h : ∀ j ∈ range (r+1),
      P.coeff j * ((r+1-j+(n+1)).choose (n+1) : ℚ) -
      P.coeff j * ((r-j+(n+1)).choose (n+1) : ℚ) =
      P.coeff j * ((r+1-j+n).choose n : ℚ) := by
    intro j hj
    have hjr : j ≤ r := Nat.le_of_lt_succ (mem_range.mp hj)
    have he : r+1-j = r-j+1 := by omega
    rw [he]
    rw [show r-j+1+(n+1) = (r-j+(n+1))+1 by omega, Nat.choose_succ_succ]
    push_cast
    simp only [Nat.succ_eq_add_one]
    have he' : r-j+1+n = r-j+(n+1) := by omega
    rw [he']
    ring
  have hh := Finset.sum_congr rfl h
  rw [Finset.sum_sub_distrib] at hh
  simp only [Nat.sub_self, zero_add, Nat.choose_self, Nat.cast_one, mul_one] at *
  linarith

theorem hilbertConvolution_cancel (P : Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution ((1-X)*P) (n+1) r = hilbertConvolution P n r := by
  rw [sub_mul, one_mul, hilbertConvolution_sub]
  cases r with
  | zero => simp
  | succ r => rw [hilbertConvolution_X_mul_succ]; exact hilbertConvolution_pascal P n r

theorem hilbertConvolution_cancel_pow (c n r : ℕ) (hc : c ≤ n) :
    hilbertConvolution ((1-X)^c) n r = ((r+n-c).choose (n-c) : ℚ) := by
  induction c generalizing n with
  | zero => simp
  | succ c ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ', hilbertConvolution_cancel, ih n (by omega)]
    rw [show r+(n+1)-(c+1) = r+n-c by omega,
      show n+1-(c+1) = n-c by omega]


theorem hilbertConvolution_sum {α : Type*} (s : Finset α)
    (f : α → Polynomial ℚ) (n r : ℕ) :
    hilbertConvolution (∑ a ∈ s, f a) n r =
      ∑ a ∈ s, hilbertConvolution (f a) n r := by
  simp only [hilbertConvolution, finsetSum_coeff, Finset.sum_mul]
  exact Finset.sum_comm

/-- Evaluation about z=1 in the basis (1-z)^i. -/
theorem polynomial_at_one_expansion (P : Polynomial ℚ) (n : ℕ)
    (hP : (P.comp (1+X)).natDegree ≤ n) :
    P = ∑ i ∈ range (n+1), C ((-1 : ℚ)^i * (P.comp (1+X)).coeff i) * (1-X)^i := by
  have hp := (P.comp (1+X)).as_sum_range_C_mul_X_pow' (by omega :
    (P.comp (1+X)).natDegree < n+1)
  have he := congrArg (fun Q : Polynomial ℚ => Q.comp (X-1)) hp
  have hs : (1+X : Polynomial ℚ).comp (X-1) = X := by simp
  simp only [comp_assoc, hs, comp_X] at he
  conv_lhs => rw [he]
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  apply sum_congr rfl
  intro i _
  have hx : (X-1 : Polynomial ℚ) = -(1-X) := by ring
  rw [hx, neg_pow]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- The finite coefficient-convolution version of the all-s Hilbert expansion. -/
theorem hilbertConvolution_expansion (P : Polynomial ℚ) (n r : ℕ)
    (hP : (P.comp (1+X)).natDegree ≤ n) :
    hilbertConvolution P n r = ∑ i ∈ range (n+1),
      (-1 : ℚ)^i * (P.comp (1+X)).coeff i * ((r+n-i).choose (n-i) : ℚ) := by
  conv_lhs => arg 1; rw [polynomial_at_one_expansion P n hP]
  rw [hilbertConvolution_sum]
  apply sum_congr rfl
  intro i hi
  rw [hilbertConvolution_C_mul, hilbertConvolution_cancel_pow i n r (by
    have := mem_range.mp hi
    omega)]

end HilbertBipartite
