import Mathlib.Data.List.Permutation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

namespace ResearchMain.EulerianPencil

open Polynomial

def descentCount : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (if b < a then 1 else 0) + descentCount (b :: l)

theorem descentCount_cons_cons (a b : ℕ) (l : List ℕ) :
    descentCount (a :: b :: l) = (if b < a then 1 else 0) + descentCount (b :: l) := rfl

theorem descentCount_prefix_le (a : ℕ) (l : List ℕ) : descentCount (a :: l) ≤ l.length := by
  induction l generalizing a with
  | nil => simp [descentCount]
  | cons b l ih =>
    rw [descentCount_cons_cons]
    have h := ih b
    split_ifs <;> simp only [List.length_cons] <;> omega

noncomputable def descentPolynomial (l : List ℕ) : ℤ[X] :=
  (l.permutations'.map (fun p => X ^ descentCount p)).sum

noncomputable def eulerian (n : ℕ) : ℤ[X] := descentPolynomial (List.range n)

theorem descentPolynomial_perm {l r : List ℕ} (h : l.Perm r) :
    descentPolynomial l = descentPolynomial r := by
  exact (h.permutations'.map (fun p => (X : ℤ[X]) ^ descentCount p)).sum_eq

theorem descentPolynomial_eval_one (l : List ℕ) : (descentPolynomial l).eval 1 = (l.length.factorial : ℤ) := by
  have hlen : l.permutations'.length = l.length.factorial := by
    rw [← (List.permutations_perm_permutations' l).length_eq, List.length_permutations]
  simp [descentPolynomial, eval_listSum, Function.comp_def, hlen]

theorem eulerian_eval_one (n : ℕ) : (eulerian n).eval 1 = (n.factorial : ℤ) := by
  simpa only [eulerian, List.length_range] using descentPolynomial_eval_one (List.range n)

theorem eulerian_zero : eulerian 0 = 1 := by simp [eulerian, descentPolynomial, descentCount]

theorem eulerian_one : eulerian 1 = 1 := by simp [eulerian, descentPolynomial, descentCount, List.range_succ]

end ResearchMain.EulerianPencil
