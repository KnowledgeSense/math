import HilbertBipartite.HilbertExpansion

open Finset Polynomial
namespace HilbertBipartite

/-- Numerator for the lengths of the powers of the square of the maximal ideal. -/
noncomputable def squareNumerator : ℕ → Polynomial ℚ
  | 0 => 1
  | 1 => C 2
  | n+2 => C 2 * squareNumerator (n+1) - (1-X)*squareNumerator n

@[simp] theorem squareNumerator_constant (n : ℕ) :
    (squareNumerator n).coeff 0 = (n+1 : ℕ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [squareNumerator]
  | one => simp [squareNumerator]
  | more n h0 h1 =>
    rw [squareNumerator, coeff_sub, coeff_C_mul]
    simp only [coeff_mul, Nat.antidiagonal_zero, Finset.sum_singleton, coeff_sub, coeff_one,
      coeff_X_zero, sub_zero, h0, h1]
    push_cast
    ring

/-- The square-maximal-ideal numerator gives the length in every positive degree. -/
theorem squareNumerator_convolution (n r : ℕ) :
    hilbertConvolution (squareNumerator n) n r = ((2*r+n+1).choose n : ℚ) := by
  induction n using Nat.twoStepInduction generalizing r with
  | zero => simp [squareNumerator]
  | one =>
    rw [squareNumerator, show C (2:ℚ) = C 2 * (1 : Polynomial ℚ) by ring,
      hilbertConvolution_C_mul, hilbertConvolution_one]
    simp only [Nat.choose_one_right]
    push_cast
    ring
  | more n hn hn1 =>
    induction r with
    | zero => simp [Nat.choose_succ_self_right]
    | succ r hr =>
      have hp := hilbertConvolution_pascal (squareNumerator (n+2)) (n+1) r
      rw [show n+1+1=n+2 by omega] at hp
      conv_rhs at hp =>
        rw [squareNumerator, hilbertConvolution_sub, hilbertConvolution_C_mul,
          hilbertConvolution_cancel]
      rw [hn, hn1] at hp
      have hb : ((2*(r+1)+n+2+1).choose (n+2) : ℚ) -
          ((2*r+n+2+1).choose (n+2) : ℚ) =
          2 * ((2*(r+1)+n+1+1).choose (n+1) : ℚ) -
          ((2*(r+1)+n+1).choose n : ℚ) := by
        have h1 := Nat.choose_succ_succ (2*r+n+4) (n+1)
        have h2 := Nat.choose_succ_succ (2*r+n+3) (n+1)
        have h3 := Nat.choose_succ_succ (2*r+n+3) n
        have h1' := congrArg (fun a : ℕ => (a : ℚ)) h1
        have h2' := congrArg (fun a : ℕ => (a : ℚ)) h2
        have h3' := congrArg (fun a : ℕ => (a : ℚ)) h3
        push_cast at h1' h2' h3'
        simp only [Nat.succ_eq_add_one] at h1' h2' h3'
        rw [show 2*(r+1)+n+2+1=2*r+n+4+1 by omega,
          show 2*r+n+2+1=2*r+n+3 by omega,
          show 2*(r+1)+n+1+1=2*r+n+3+1 by omega,
          show 2*(r+1)+n+1=2*r+n+3 by omega]
        linarith
      rw [hr] at hp
      simp only [Nat.add_assoc] at hp hb ⊢
      linarith

end HilbertBipartite
