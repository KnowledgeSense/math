import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace GenericValueSemigroups
open scoped BigOperators

/-- A bounded exponent vector encoded by its digits in base `b`. -/
def digitWeight {d : ℕ} (b : ℕ) (α : Fin d → ℕ) : ℕ := ∑ i, α i * b ^ i.val

@[simp] theorem digitWeight_zero {d : ℕ} (b : ℕ) :
    digitWeight b (fun _ : Fin d => 0) = 0 := by simp [digitWeight]

theorem digitWeight_succ {d : ℕ} (b : ℕ) (α : Fin (d+1) → ℕ) :
    digitWeight b α = α 0 + b * digitWeight b (fun i => α i.succ) := by
  simp only [digitWeight, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem digitWeight_lt {d : ℕ} (b : ℕ) (_hb : 0 < b) (α : Fin d → ℕ)
    (hα : ∀ i, α i < b) : digitWeight b α < b ^ d := by
  induction d with
  | zero => simp [digitWeight]
  | succ d ih =>
    rw [digitWeight_succ, pow_succ, Nat.mul_comm (b ^ d) b]
    have ht := ih (fun i => α i.succ) (fun i => hα i.succ)
    calc
      α 0 + b * digitWeight b (fun i => α i.succ) <
          b + b * digitWeight b (fun i => α i.succ) := Nat.add_lt_add_right (hα 0) _
      _ = b * (digitWeight b (fun i => α i.succ) + 1) := by ring
      _ ≤ b * b ^ d := Nat.mul_le_mul_left b ht

theorem digitWeight_injective_on_bounded {d : ℕ} (b : ℕ) (hb : 0 < b)
    (α β : Fin d → ℕ) (hα : ∀ i, α i < b) (hβ : ∀ i, β i < b)
    (h : digitWeight b α = digitWeight b β) : α = β := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    rw [digitWeight_succ, digitWeight_succ] at h
    have h0 : α 0 = β 0 := by
      have hm := congrArg (fun n => n % b) h
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (hα 0), Nat.mod_eq_of_lt (hβ 0)] using hm
    have ht : digitWeight b (fun i => α i.succ) = digitWeight b (fun i => β i.succ) := by
      rw [h0, Nat.add_right_inj] at h
      exact Nat.eq_of_mul_eq_mul_left hb h
    have he := ih (fun i => α i.succ) (fun i => β i.succ)
      (fun i => hα i.succ) (fun i => hβ i.succ) ht
    funext i
    exact Fin.cases h0 (fun j => congrFun he j) i

end GenericValueSemigroups
