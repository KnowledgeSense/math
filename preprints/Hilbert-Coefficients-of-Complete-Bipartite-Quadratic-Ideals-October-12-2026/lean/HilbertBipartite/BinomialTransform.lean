import HilbertBipartite.CorrectionNumerator

open Finset Polynomial
namespace HilbertBipartite

/-- Finite binomial transform of a sequence of polynomials. -/
noncomputable def binomialTransform (f : ℕ → Polynomial ℚ) (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ range (n+1), C (n.choose k : ℚ) * f k

@[simp] theorem binomialTransform_zero (f : ℕ → Polynomial ℚ) :
    binomialTransform f 0 = f 0 := by simp [binomialTransform]

theorem binomialTransform_add (f g : ℕ → Polynomial ℚ) (n : ℕ) :
    binomialTransform (fun k => f k + g k) n = binomialTransform f n + binomialTransform g n := by
  simp only [binomialTransform, mul_add, sum_add_distrib]

theorem binomialTransform_sub (f g : ℕ → Polynomial ℚ) (n : ℕ) :
    binomialTransform (fun k => f k - g k) n = binomialTransform f n - binomialTransform g n := by
  simp only [binomialTransform, mul_sub, sum_sub_distrib]

theorem binomialTransform_mul (P : Polynomial ℚ) (f : ℕ → Polynomial ℚ) (n : ℕ) :
    binomialTransform (fun k => P * f k) n = P * binomialTransform f n := by
  simp only [binomialTransform, mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem binomialTransform_succ (f : ℕ → Polynomial ℚ) (n : ℕ) :
    binomialTransform f (n+1) =
      binomialTransform f n + binomialTransform (fun k => f (k+1)) n := by
  unfold binomialTransform
  conv_lhs => rw [sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, map_one, one_mul,
    Nat.choose_succ_succ, Nat.cast_add, map_add, add_mul, sum_add_distrib]
  have h : (∑ k ∈ range (n+1), C (n.choose (k+1) : ℚ) * f (k+1)) + f 0 =
      ∑ k ∈ range (n+1), C (n.choose k : ℚ) * f k := by
    conv_lhs => lhs; rw [sum_range_succ]
    conv_rhs => rw [sum_range_succ']
    simp
  simp only [Nat.succ_eq_add_one]
  rw [← h]
  ring

theorem binomialTransform_one (n : ℕ) :
    binomialTransform (fun _ => (1 : Polynomial ℚ)) n = C (2^n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [binomialTransform_succ, ih, pow_succ]
    simp only [map_mul, map_ofNat]
    ring

end HilbertBipartite
