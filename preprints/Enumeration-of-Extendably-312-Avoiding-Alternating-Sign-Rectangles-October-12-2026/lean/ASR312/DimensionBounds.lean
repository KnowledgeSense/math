import ASR312.Sums
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ASR312

 theorem row_nonzeroEntries_empty_iff {r k : ℕ} (A : Rectangle r k) (i : Fin r) :
    nonzeroEntries (row A i) = [] ↔ ∀ j, A i j = .zero := by
  simp [nonzeroEntries,row,List.filter_eq_nil_iff]

 theorem row_entrySum {r k : ℕ} (A : Rectangle r k) (i : Fin r) :
    entrySum (row A i) = ∑ j, (A i j).value := by
  simp [entrySum,row,List.sum_ofFn]

 theorem col_entrySum {r k : ℕ} (A : Rectangle r k) (j : Fin k) :
    entrySum (col A j) = ∑ i, (A i j).value := by
  simp [entrySum,col,List.sum_ofFn]

 theorem total_sum_nonemptyRows {r k : ℕ} (A : Rectangle r k) (h : IsASR A) :
    ∑ i, ∑ j, (A i j).value = (nonemptyRows A : ℤ) := by
  classical
  have hi (i : Fin r) : (∑ j, (A i j).value) = if ∃ j, A i j ≠ .zero then 1 else 0 := by
    rw [← row_entrySum,row_sum_one_or_zero _ (h.1 i).1 (h.1 i).2.1 (h.1 i).2.2]
    simp only [row_nonzeroEntries_empty_iff]
    by_cases hh : ∃ j, A i j ≠ .zero <;> simp_all
  simp_rw [hi]
  simp [nonemptyRows]

 theorem nonemptyRows_le_columns {r k : ℕ} (A : Rectangle r k) (h : IsASR A) :
    nonemptyRows A ≤ k := by
  have hh : (nonemptyRows A : ℤ) ≤ k := by
    rw [← total_sum_nonemptyRows A h,Finset.sum_comm]
    calc
      (∑ j, ∑ i, (A i j).value) ≤ ∑ _j : Fin k, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← col_entrySum]
        exact (column_sum_bounds _ (h.2 j).1 (h.2 j).2).2
      _ = k := by simp
  exact_mod_cast hh

 theorem nonemptyRows_le_rows {r k : ℕ} (A : Rectangle r k) : nonemptyRows A ≤ r := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

 theorem S_eq_zero_of_rows_lt {r k d : ℕ} (h : r < d) : S r k d = 0 := by
  classical
  unfold S
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun A => by have hh := nonemptyRows_le_rows A.val; rw [A.property.2.1] at hh; omega⟩

 theorem S_eq_zero_of_columns_lt {r k d : ℕ} (h : k < d) : S r k d = 0 := by
  classical
  unfold S
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun A => by have hh := nonemptyRows_le_columns A.val A.property.1; rw [A.property.2.1] at hh; omega⟩

end ASR312
