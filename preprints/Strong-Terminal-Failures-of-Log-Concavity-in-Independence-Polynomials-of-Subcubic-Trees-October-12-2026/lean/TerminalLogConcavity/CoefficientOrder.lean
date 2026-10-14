import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

/-- Coefficientwise order on polynomials with natural coefficients. -/
def CoeffLE (p q : ℕ[X]) : Prop := ∀ n, p.coeff n ≤ q.coeff n

namespace CoeffLE

theorem refl (p : ℕ[X]) : CoeffLE p p := fun _ => le_rfl

theorem trans {p q r : ℕ[X]} (hpq : CoeffLE p q) (hqr : CoeffLE q r) : CoeffLE p r :=
  fun n => (hpq n).trans (hqr n)

theorem add {p q r s : ℕ[X]} (hpq : CoeffLE p q) (hrs : CoeffLE r s) :
    CoeffLE (p + r) (q + s) := by
  intro n
  simpa only [coeff_add] using Nat.add_le_add (hpq n) (hrs n)

theorem mul {p q r s : ℕ[X]} (hpq : CoeffLE p q) (hrs : CoeffLE r s) :
    CoeffLE (p * r) (q * s) := by
  intro n
  simp only [coeff_mul]
  apply Finset.sum_le_sum
  intro ij _
  exact Nat.mul_le_mul (hpq ij.1) (hrs ij.2)

theorem pow {p q : ℕ[X]} (hpq : CoeffLE p q) (n : ℕ) : CoeffLE (p ^ n) (q ^ n) := by
  induction n with
  | zero => exact refl _
  | succ n ih => simpa only [pow_succ] using mul ih hpq

theorem prod {ι : Type*} {s : Finset ι} {f g : ι → ℕ[X]}
    (h : ∀ i ∈ s, CoeffLE (f i) (g i)) : CoeffLE (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact refl _
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

theorem le_add_right (p q : ℕ[X]) : CoeffLE p (p + q) := by
  intro n
  simp only [coeff_add]
  omega

theorem le_mul_one_add (p q : ℕ[X]) : CoeffLE p (p * (1 + q)) := by
  simpa only [mul_add, mul_one] using le_add_right p (p * q)

theorem constant_le (p : ℕ[X]) : CoeffLE (C (p.coeff 0)) p := by
  intro n
  by_cases hn : n = 0
  · subst n; simp
  · simp [hn]

end CoeffLE
end TerminalLogConcavity
