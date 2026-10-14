import MainTheorems.AHOConstants.ClosedWalkProducts
import Mathlib.Analysis.Complex.Basic

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def realCastMatrix (M : Matrix I I ℝ) : Matrix I I ℂ :=
  M.map (algebraMap ℝ ℂ)

def EntryNonnegative (M : Matrix I I ℝ) : Prop := ∀ i j, 0 ≤ M i j

omit [Fintype I] in
theorem realCastMatrix_one : realCastMatrix (1 : Matrix I I ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [realCastMatrix, Matrix.one_apply, h]

omit [DecidableEq I] in
theorem realCastMatrix_mul (M N : Matrix I I ℝ) :
    realCastMatrix (M * N) = realCastMatrix M * realCastMatrix N := Matrix.map_mul

omit [Fintype I] in
theorem realCastMatrix_diagonal (v : I → ℝ) :
    realCastMatrix (Matrix.diagonal v) = Matrix.diagonal (fun i => (v i : ℂ)) := by
  ext i j
  by_cases h : i = j <;> simp [realCastMatrix, h]

omit [Fintype I] [DecidableEq I] in
theorem realCastMatrix_re {M : Matrix I I ℂ} (hM : ∀ i j, (M i j).im = 0) :
    realCastMatrix (fun i j => (M i j).re) = M := by
  ext i j
  apply Complex.ext
  · rfl
  · exact (hM i j).symm

theorem realCastMatrix_product (xs : List (Matrix I I ℝ)) :
    (xs.map realCastMatrix).prod = realCastMatrix xs.prod := by
  induction xs with
  | nil => exact realCastMatrix_one.symm
  | cons M xs ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih, ← realCastMatrix_mul]

omit [DecidableEq I] in
theorem realCastMatrix_trace (M : Matrix I I ℝ) :
    Matrix.trace (realCastMatrix M) = ((Matrix.trace M : ℝ) : ℂ) :=
  (AddMonoidHom.map_trace (algebraMap ℝ ℂ) M).symm

omit [Fintype I] in
theorem entryNonnegative_one : EntryNonnegative (1 : Matrix I I ℝ) := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

omit [DecidableEq I] in
theorem EntryNonnegative.mul {M N : Matrix I I ℝ} (hM : EntryNonnegative M)
    (hN : EntryNonnegative N) : EntryNonnegative (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun t ht => mul_nonneg (hM i t) (hN t j))

theorem entryNonnegative_product (xs : List (Matrix I I ℝ))
    (h : ∀ M ∈ xs, EntryNonnegative M) : EntryNonnegative xs.prod := by
  revert h
  induction xs with
  | nil => intro _; exact entryNonnegative_one
  | cons M xs ih =>
    intro h
    exact (h M (by simp)).mul (ih (fun N hN => h N (by simp [hN])))

omit [DecidableEq I] in
theorem EntryNonnegative.trace {M : Matrix I I ℝ} (hM : EntryNonnegative M) :
    0 ≤ Matrix.trace M := Finset.sum_nonneg (fun i _hi => hM i i)

theorem realCastMatrix_product_trace_norm (xs : List (Matrix I I ℝ))
    (h : ∀ M ∈ xs, EntryNonnegative M) :
    ‖Matrix.trace ((xs.map realCastMatrix).prod)‖ = Matrix.trace xs.prod := by
  rw [realCastMatrix_product, realCastMatrix_trace, Complex.norm_real]
  exact Real.norm_of_nonneg (entryNonnegative_product xs h).trace

theorem closed_walk_term_le_trace (M : Matrix I I ℝ) (xs : List (Matrix I I ℝ))
    (h : ∀ N ∈ M :: xs, EntryNonnegative N) (f : Fin (xs.length + 1) → I) :
    (∏ i : Fin (xs.length + 1), (M :: xs).get i (f i) (f (finRotate _ i))) ≤
      Matrix.trace (M :: xs).prod := by
  rw [closed_walk_trace_product]
  apply Finset.single_le_sum _ (Finset.mem_univ f)
  intro g hg
  apply Finset.prod_nonneg
  intro i hi
  exact h _ (List.get_mem (M :: xs) i) _ _

theorem closed_walk_term_le_trace_ofFn {m : ℕ} (M : Fin (m + 1) → Matrix I I ℝ)
    (h : ∀ i, EntryNonnegative (M i)) (f : Fin (m + 1) → I) :
    (∏ i : Fin (m + 1), M i (f i) (f (finRotate _ i))) ≤
      Matrix.trace (List.ofFn M).prod := by
  rw [closed_walk_trace_ofFn]
  apply Finset.single_le_sum _ (Finset.mem_univ f)
  intro g hg
  exact Finset.prod_nonneg (fun i hi => h i _ _)

end ResearchMain.AHOConstants
