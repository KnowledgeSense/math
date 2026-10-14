import MainTheorems.EulerianPencil.Insertion

namespace ResearchMain.EulerianPencil

open Polynomial

theorem descentCount_le_length (l : List ℕ) : descentCount l ≤ l.length := by
  cases l with
  | nil => simp [descentCount]
  | cons a l => exact (descentCount_prefix_le a l).trans (by simp)

theorem X_derivative_monomial (d : ℕ) :
    X * derivative (X ^ d : ℤ[X]) = (d : ℤ[X]) * X ^ d := by
  cases d with
  | zero => simp
  | succ d =>
    rw [derivative_X_pow_succ, pow_succ]
    simp only [map_add, map_natCast, map_one]
    push_cast
    ring

theorem insertion_monomial_identity {d m : ℕ} (hd : d ≤ m) :
    ((d + 1 : ℕ) : ℤ[X]) * X ^ d + ((m - d : ℕ) : ℤ[X]) * X ^ (d + 1) =
      (1 + (m : ℤ[X]) * X) * X ^ d + X * (1 - X) * derivative (X ^ d) := by
  have he : X * (1 - X) * derivative (X ^ d : ℤ[X]) =
      (1 - X) * (X * derivative (X ^ d)) := by ring
  rw [he, X_derivative_monomial, Nat.cast_sub hd, pow_succ]
  push_cast
  ring

theorem polynomial_flatMap_sum {α : Type} (l : List α) (f : α → List (List ℕ)) :
    ((l.flatMap f).map (fun p => (X : ℤ[X]) ^ descentCount p)).sum =
      (l.map (fun a => ((f a).map (fun p => (X : ℤ[X]) ^ descentCount p)).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem descentPolynomial_cons (n : ℕ) (l : List ℕ) (hmax : ∀ a ∈ l, a < n) :
    descentPolynomial (n :: l) =
      (1 + (l.length : ℤ[X]) * X) * descentPolynomial l +
        X * (1 - X) * derivative (descentPolynomial l) := by
  have hterm (p : List ℕ) (hp : p ∈ l.permutations') :
      ((List.permutations'Aux n p).map (fun v => (X : ℤ[X]) ^ descentCount v)).sum =
        (1 + (l.length : ℤ[X]) * X) * X ^ descentCount p +
          X * (1 - X) * derivative (X ^ descentCount p) := by
    have hperm := List.mem_permutations'.mp hp
    rw [insertion_generating_function n p
      (fun a ha => hmax a (hperm.mem_iff.mp ha)), ← insertion_monomial_identity]
    · rw [hperm.length_eq]
    · rw [← hperm.length_eq]
      exact descentCount_le_length p
  unfold descentPolynomial
  rw [List.permutations', polynomial_flatMap_sum]
  have hmap := List.map_congr_left hterm
  rw [hmap]
  rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
  congr 1
  simp only [map_list_sum, List.map_map, Function.comp_def]

theorem eulerian_recurrence (n : ℕ) :
    eulerian (n + 1) = (1 + (n : ℤ[X]) * X) * eulerian n +
      X * (1 - X) * derivative (eulerian n) := by
  have hperm : (List.range (n + 1)).Perm (n :: List.range n) := by
    rw [List.range_succ]
    exact List.perm_append_comm
  rw [eulerian, descentPolynomial_perm hperm,
    descentPolynomial_cons n (List.range n) (fun a ha => List.mem_range.mp ha), List.length_range]
  rfl

end ResearchMain.EulerianPencil
