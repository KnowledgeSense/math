import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

open scoped BigOperators

def activeCoordinate (i : Fin 2) : Fin 3 := if i = 0 then 0 else 2

def activeCompression {R : Type*} (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R :=
  M.submatrix activeCoordinate activeCoordinate

def MiddleColumnZero {R : Type*} [Zero R] (M : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i, M i 1 = 0

variable {R : Type*} [Semiring R]

theorem activeCompression_one : activeCompression (1 : Matrix (Fin 3) (Fin 3) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [activeCompression, activeCoordinate]

theorem activeCompression_mul (M N : Matrix (Fin 3) (Fin 3) R) (hM : MiddleColumnZero M) :
    activeCompression (M * N) = activeCompression M * activeCompression N := by
  change ∀ i, M i 1 = 0 at hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [activeCompression, activeCoordinate, Matrix.mul_apply, Fin.sum_univ_succ, hM]

theorem middleColumnZero_product (M : Matrix (Fin 3) (Fin 3) R)
    (xs : List (Matrix (Fin 3) (Fin 3) R))
    (h : ∀ N ∈ M :: xs, MiddleColumnZero N) : MiddleColumnZero (M :: xs).prod := by
  revert h
  induction xs generalizing M with
  | nil => intro h; simpa only [List.prod_cons, List.prod_nil, Matrix.mul_one] using h M (by simp)
  | cons N xs ih =>
    intro h
    have ht := ih N (fun X hX => h X (by simp [hX]))
    change ∀ i, (N :: xs).prod i 1 = 0 at ht
    intro i
    change (M * (N :: xs).prod) i 1 = 0
    rw [Matrix.mul_apply]
    simp only [ht, mul_zero, Finset.sum_const_zero]

theorem activeCompression_product (xs : List (Matrix (Fin 3) (Fin 3) R))
    (h : ∀ M ∈ xs, MiddleColumnZero M) :
    activeCompression xs.prod = (xs.map activeCompression).prod := by
  revert h
  induction xs with
  | nil => intro _; exact activeCompression_one
  | cons M xs ih =>
    intro h
    rw [List.prod_cons, activeCompression_mul M _ (h M (by simp)),
      ih (fun N hN => h N (by simp [hN]))]
    rfl

theorem trace_activeCompression (M : Matrix (Fin 3) (Fin 3) R) (hM : MiddleColumnZero M) :
    Matrix.trace M = Matrix.trace (activeCompression M) := by
  change ∀ i, M i 1 = 0 at hM
  simp [Matrix.trace, Matrix.diag_apply, activeCompression, activeCoordinate,
    Fin.sum_univ_succ, hM]

theorem trace_activeCompression_product (M : Matrix (Fin 3) (Fin 3) R)
    (xs : List (Matrix (Fin 3) (Fin 3) R))
    (h : ∀ N ∈ M :: xs, MiddleColumnZero N) :
    Matrix.trace (M :: xs).prod = Matrix.trace (((M :: xs).map activeCompression).prod) := by
  rw [trace_activeCompression _ (middleColumnZero_product M xs h), activeCompression_product _ h]

theorem trace_activeCompression_product_nonempty (xs : List (Matrix (Fin 3) (Fin 3) R))
    (hne : xs ≠ []) (h : ∀ N ∈ xs, MiddleColumnZero N) :
    Matrix.trace xs.prod = Matrix.trace ((xs.map activeCompression).prod) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons M xs => exact trace_activeCompression_product M xs h

end ResearchMain.AHOConstants
