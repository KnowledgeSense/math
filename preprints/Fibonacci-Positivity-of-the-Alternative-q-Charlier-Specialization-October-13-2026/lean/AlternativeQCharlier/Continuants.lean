import AlternativeQCharlier.Definitions

namespace AlternativeQCharlier
noncomputable section

/-- A continuant calculated by expansion at its first row. -/
def continuant (a b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, 1 => a m
  | m, n+2 => a m * continuant a b (m+1) (n+1) -
      b m * continuant a b (m+2) n

@[simp] theorem tridiagonal_diag (a b : ℕ → ℝ) (n : ℕ) (i : Fin n) :
    tridiagonal a b n i i = a i := by simp [tridiagonal]

 theorem tridiagonal_tail (a b : ℕ → ℝ) (n : ℕ) :
    (tridiagonal a b (n+1)).submatrix Fin.succ Fin.succ =
      tridiagonal (fun i => a (i+1)) (fun i => b (i+1)) n := by
  ext i j
  simp [Matrix.submatrix_apply, tridiagonal, Fin.succ_inj]

 theorem tridiagonal_first_row_far (a b : ℕ → ℝ) (n : ℕ) (j : Fin n) :
    tridiagonal a b (n+2) 0 j.succ.succ = 0 := by
  simp [tridiagonal, Fin.ext_iff]

 theorem tridiagonal_det_recurrence (a b : ℕ → ℝ) (n : ℕ) :
    (tridiagonal a b (n+2)).det =
      a 0 * (tridiagonal (fun i => a (i+1)) (fun i => b (i+1)) (n+1)).det -
      b 0 * (tridiagonal (fun i => a (i+2)) (fun i => b (i+2)) n).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
    tridiagonal_diag, Fin.val_succ, zero_add, pow_one,
    tridiagonal_first_row_far, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [tridiagonal_tail]
  have hminor :
      ((tridiagonal a b (n+2)).submatrix Fin.succ (1 : Fin (n+2)).succAbove).det =
        (tridiagonal (fun i => a (i+2)) (fun i => b (i+2)) n).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hzero : ∀ i : Fin n,
        ((tridiagonal a b (n+2)).submatrix Fin.succ
          (1 : Fin (n+2)).succAbove) i.succ 0 = 0 := by
      intro i
      simp [Matrix.submatrix_apply, tridiagonal, Fin.succAbove, Fin.ext_iff]
    simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
      Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have hone : ((tridiagonal a b (n+2)).submatrix Fin.succ
        (1 : Fin (n+2)).succAbove) 0 0 = 1 := by
      simp [Matrix.submatrix_apply, tridiagonal, Fin.succAbove]
    rw [hone, one_mul]
    congr 1
    ext i j
    simp [Matrix.submatrix_apply, tridiagonal, Fin.succAbove, Fin.ext_iff]
  simp only [Fin.succ_zero_eq_one]
  rw [hminor]
  have hsuper : tridiagonal a b (n+2) 0 1 = b 0 := by
    simp [tridiagonal]
  rw [hsuper]
  ring

 theorem A_eq_continuant (a b : ℕ → ℝ) (m n : ℕ) :
    A a b m n = continuant a b m n := by
  induction n using Nat.twoStepInduction generalizing m with
  | zero => simp [A, continuant, Matrix.det_isEmpty]
  | one => simp [A, continuant, Matrix.det_unique, tridiagonal]
  | more n ih ih' =>
    simp only [A, tridiagonal_det_recurrence, continuant]
    simpa only [A, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using
      congrArg₂ (fun x y => a m*x-b m*y) (ih' (m+1)) (ih (m+2))

@[simp] theorem B_zero (a b : ℕ → ℝ) (m : ℕ) : B a b m 0 = b m := by
  simp [B, Matrix.det_unique, tridiagonal]

 theorem B_succ (a b : ℕ → ℝ) (m n : ℕ) :
    B a b m (n+1) = b m * A a b (m+2) (n+1) -
      a m*b (m+1)*A a b (m+3) n := by
  simp only [B, tridiagonal_det_recurrence]
  simp [A, Nat.add_comm, Nat.add_left_comm]

/-- The product of the positive diagonal rescaling factors on an interval. -/
def scaleProduct (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, n+1 => c m*scaleProduct c (m+1) n

 theorem scaleProduct_pos (c : ℕ → ℝ) (h : ∀ i, 0 < c i) (m n : ℕ) :
    0 < scaleProduct c m n := by
  induction n generalizing m with
  | zero => norm_num [scaleProduct]
  | succ n ih => exact mul_pos (h m) (ih (m+1))

 theorem continuant_rescaling (a b c : ℕ → ℝ) (m n : ℕ) :
    continuant (fun i => c i*a i) (fun i => c i*c (i+1)*b i) m n =
      scaleProduct c m n * continuant a b m n := by
  induction n using Nat.twoStepInduction generalizing m with
  | zero => simp [continuant, scaleProduct]
  | one => simp [continuant, scaleProduct]
  | more n ih ih' =>
    simp only [continuant, ih, ih', scaleProduct, Nat.add_assoc, Nat.reduceAdd]
    ring

 theorem A_rescaling (a b c : ℕ → ℝ) (m n : ℕ) :
    A (fun i => c i*a i) (fun i => c i*c (i+1)*b i) m n =
      scaleProduct c m n * A a b m n := by
  simp only [A_eq_continuant, continuant_rescaling]

 theorem B_rescaling (a b c : ℕ → ℝ) (m n : ℕ) :
    B (fun i => c i*a i) (fun i => c i*c (i+1)*b i) m n =
      scaleProduct c m (n+2) * B a b m n := by
  cases n with
  | zero => simp [B_zero, scaleProduct]
  | succ n =>
    simp only [B_succ, A_rescaling, scaleProduct, Nat.add_assoc, Nat.reduceAdd]
    ring

end
end AlternativeQCharlier
