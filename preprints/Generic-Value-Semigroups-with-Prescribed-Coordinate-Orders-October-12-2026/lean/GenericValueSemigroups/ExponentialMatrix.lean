import GenericValueSemigroups.PascalMatrix
import Mathlib.Tactic.FieldSimp

namespace GenericValueSemigroups
open Matrix Finset

/-- The finite lower triangular exponential coefficient matrix. -/
noncomputable def exponentialMatrix (N : ℕ) (s : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if j ≤ i then s ^ (i.val-j.val) / (Nat.factorial (i.val-j.val) : ℝ) else 0

theorem exponentialMatrix_factor_entry {N : ℕ} {s : ℝ} (hs : s ≠ 0)
    (i j : Fin N) : exponentialMatrix N s i j =
      (s^i.val / (Nat.factorial i.val : ℝ)) *
      ((Nat.factorial j.val : ℝ) / s^j.val) * pascalStage N N i j := by
  by_cases h : j ≤ i
  · simp only [exponentialMatrix, pascalStage, ite_eq_left h,
      Nat.min_eq_left (Nat.le_of_lt i.isLt)]
    have hij : j.val ≤ i.val := h
    have hc : (i.val.choose (i.val-j.val) : ℝ) *
        (Nat.factorial (i.val-j.val) : ℝ) * (Nat.factorial j.val : ℝ) =
        (Nat.factorial i.val : ℝ) := by
      exact_mod_cast (by simpa [Nat.sub_sub_self hij] using
        Nat.choose_mul_factorial_mul_factorial (Nat.sub_le i.val j.val))
    have hp : s^i.val = s^(i.val-j.val)*s^j.val := by
      rw [← pow_add, Nat.sub_add_cancel hij]
    have hi : (Nat.factorial i.val : ℝ) ≠ 0 := by positivity
    have hj : (Nat.factorial (i.val-j.val) : ℝ) ≠ 0 := by positivity
    field_simp
    rw [hp]
    rw [← hc]
    ring
  · simp [exponentialMatrix, pascalStage, h]

theorem exponentialMatrix_minor_factor {N q : ℕ} {s : ℝ} (hs : s ≠ 0)
    (rows cols : Fin q → Fin N) :
    ((exponentialMatrix N s).submatrix rows cols).det =
      (∏ i, s^(rows i).val / (Nat.factorial (rows i).val : ℝ)) *
      (∏ i, (Nat.factorial (cols i).val : ℝ) / s^(cols i).val) *
      ((pascalStage N N).submatrix rows cols).det := by
  have he : (exponentialMatrix N s).submatrix rows cols = Matrix.of (fun i j =>
      (s^(rows i).val / (Nat.factorial (rows i).val : ℝ)) *
      (((Nat.factorial (cols j).val : ℝ) / s^(cols j).val) *
      pascalStage N N (rows i) (cols j))) := by
    ext i j
    simpa only [Matrix.submatrix_apply, Matrix.of_apply, mul_assoc] using
      exponentialMatrix_factor_entry hs (rows i) (cols j)
  rw [he]
  have h1 := Matrix.det_mul_column
    (fun i => s^(rows i).val / (Nat.factorial (rows i).val : ℝ))
    (Matrix.of fun i j => ((Nat.factorial (cols j).val : ℝ) / s^(cols j).val) *
      pascalStage N N (rows i) (cols j))
  have h2 := Matrix.det_mul_row
    (fun j => (Nat.factorial (cols j).val : ℝ) / s^(cols j).val)
    ((pascalStage N N).submatrix rows cols)
  rw [show (Matrix.of fun i j => ((Nat.factorial (cols j).val : ℝ) / s^(cols j).val) *
      pascalStage N N (rows i) (cols j)).det =
      (∏ i, (Nat.factorial (cols i).val : ℝ) / s^(cols i).val) *
      ((pascalStage N N).submatrix rows cols).det from h2] at h1
  simpa only [Matrix.of_apply, mul_assoc] using h1

theorem exponentialMatrix_totallyNonneg_pos {N : ℕ} {s : ℝ} (hs : 0 < s) :
    (exponentialMatrix N s).IsTotallyNonneg := by
  intro q rows cols hr hc
  rw [exponentialMatrix_minor_factor hs.ne']
  exact mul_nonneg (mul_nonneg
    (Finset.prod_nonneg (fun i _ => by positivity))
    (Finset.prod_nonneg (fun i _ => by positivity)))
    (pascalStage_totallyNonneg N N hr hc)

theorem exponentialMatrix_minor_pos {N q : ℕ} {s : ℝ} (hs : 0 < s)
    (rows cols : Fin q → Fin N) (hr : StrictMono rows) (hc : StrictMono cols)
    (hle : ∀ i, cols i ≤ rows i) :
    0 < ((exponentialMatrix N s).submatrix rows cols).det := by
  rw [exponentialMatrix_minor_factor hs.ne']
  apply mul_pos
  · apply mul_pos <;> apply Finset.prod_pos <;> intro i _ <;> positivity
  · apply pascalStage_minor_pos N rows cols hr hc hle
    intro i
    have := (rows i).isLt
    omega

@[simp] theorem exponentialMatrix_zero (N : ℕ) : exponentialMatrix N 0 = 1 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [exponentialMatrix]
  · have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
    by_cases hji : j ≤ i
    · have hp : i.val-j.val ≠ 0 := by omega
      simp [exponentialMatrix, h, hji, hp]
    · simp [exponentialMatrix, h, hji]

theorem exponentialMatrix_totallyNonneg {N : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    (exponentialMatrix N s).IsTotallyNonneg := by
  rcases hs.eq_or_lt with h | h
  · rw [← h, exponentialMatrix_zero]; exact Matrix.IsTotallyNonneg.one
  · exact exponentialMatrix_totallyNonneg_pos h

end GenericValueSemigroups
