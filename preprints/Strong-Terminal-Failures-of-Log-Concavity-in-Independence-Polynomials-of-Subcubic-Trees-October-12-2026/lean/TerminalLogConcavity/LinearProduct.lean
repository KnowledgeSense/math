import TerminalLogConcavity.CoefficientOrder
import Mathlib.Tactic.Linarith

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def linearProduct : List ℕ → ℕ[X]
  | [] => 1
  | d :: ds => (1 + C d * X) * linearProduct ds

theorem linearProduct_append (as bs : List ℕ) :
    linearProduct (as ++ bs) = linearProduct as * linearProduct bs := by
  induction as with
  | nil => simp [linearProduct]
  | cons a as ih => simp [linearProduct, ih, mul_assoc]

@[simp] theorem linearProduct_coeff_zero (ds : List ℕ) : (linearProduct ds).coeff 0 = 1 := by
  induction ds with
  | nil => simp [linearProduct]
  | cons d ds ih => simp [linearProduct, ih]

theorem linearProduct_coeff_succ (d : ℕ) (ds : List ℕ) (n : ℕ) :
    (linearProduct (d :: ds)).coeff (n + 1) =
      (linearProduct ds).coeff (n + 1) + d * (linearProduct ds).coeff n := by
  simp [linearProduct, add_mul, mul_assoc]

theorem linearProduct_coeff_le (ds : List ℕ) (n : ℕ) :
    (linearProduct ds).coeff n ≤ ds.sum ^ n := by
  induction ds generalizing n with
  | nil => cases n <;> simp [linearProduct, coeff_one]
  | cons d ds ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [linearProduct_coeff_succ, List.sum_cons]
      calc
        _ ≤ ds.sum ^ (n + 1) + d * ds.sum ^ n :=
          Nat.add_le_add (ih (n + 1)) (Nat.mul_le_mul_left d (ih n))
        _ = (d + ds.sum) * ds.sum ^ n := by rw [pow_succ]; ring
        _ ≤ (d + ds.sum) * (d + ds.sum) ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) n)
        _ = _ := by rw [pow_succ]; ring

end TerminalLogConcavity
