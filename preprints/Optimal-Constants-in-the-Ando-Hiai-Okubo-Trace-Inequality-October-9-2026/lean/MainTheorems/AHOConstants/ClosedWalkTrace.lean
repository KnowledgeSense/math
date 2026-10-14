import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace ResearchMain.AHOConstants

open scoped BigOperators

def headTailEquiv (n : ℕ) (I : Type*) : (Fin (n + 1) → I) ≃ I × (Fin n → I) where
  toFun f := (f 0, fun i => f i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv x := by
    apply Prod.ext
    · simp
    · funext i; simp

variable {I R : Type*} [Fintype I] [DecidableEq I] [Semiring R]

def openWalkTerm (M : Matrix I I R) :
    (xs : List (Matrix I I R)) → I → I → (Fin xs.length → I) → R
  | [], a, b, _ => M a b
  | N :: xs, a, b, f => M a (f 0) *
      openWalkTerm N xs (f 0) b (fun i => f i.succ)

def closedWalkTerm (M : Matrix I I R) (xs : List (Matrix I I R))
    (f : Fin (xs.length + 1) → I) : R :=
  openWalkTerm M xs (f 0) (f 0) (fun i => f i.succ)

theorem open_walk_entry_expansion (M : Matrix I I R) (xs : List (Matrix I I R))
    (a b : I) : (M :: xs).prod a b = ∑ f : Fin xs.length → I, openWalkTerm M xs a b f := by
  induction xs generalizing M a b with
  | nil => simp [openWalkTerm]
  | cons N xs ih =>
    calc
      (M :: N :: xs).prod a b = ∑ i : I,
          M a i * (∑ f : Fin xs.length → I, openWalkTerm N xs i b f) := by
        rw [List.prod_cons, Matrix.mul_apply]
        simp_rw [ih]
      _ = ∑ i : I, ∑ f : Fin xs.length → I, M a i * openWalkTerm N xs i b f := by
        simp only [Finset.mul_sum]
      _ = _ := by
        have h := Equiv.sum_comp (headTailEquiv xs.length I).symm
          (fun f : Fin ((N :: xs).length) → I => openWalkTerm M (N :: xs) a b f)
        change (∑ x : I × (Fin xs.length → I),
          openWalkTerm M (N :: xs) a b (Fin.cons x.1 x.2)) = _ at h
        have hη : ∀ f : Fin xs.length → I, (fun i => f i) = f := fun _ => rfl
        simp only [Fintype.sum_prod_type,
          openWalkTerm, Fin.cons_zero, Fin.cons_succ, hη] at h
        convert h using 1
        rfl

theorem closed_walk_trace_expansion (M : Matrix I I R) (xs : List (Matrix I I R)) :
    Matrix.trace (M :: xs).prod =
      ∑ f : Fin (xs.length + 1) → I, closedWalkTerm M xs f := by
  change (∑ a : I, (M :: xs).prod a a) = _
  simp_rw [open_walk_entry_expansion]
  have h := Equiv.sum_comp (headTailEquiv xs.length I).symm
    (closedWalkTerm M xs)
  change (∑ x : I × (Fin xs.length → I),
    closedWalkTerm M xs (Fin.cons x.1 x.2)) = _ at h
  simpa only [Fintype.sum_prod_type,
    closedWalkTerm, Fin.cons_zero, Fin.cons_succ] using h

end ResearchMain.AHOConstants
