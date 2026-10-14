import HankelAutomaticity.BlockElimination

noncomputable section
namespace HankelAutomaticity
open Matrix
variable {R : Type*} [CommRing R]

 def antiTriangle (r : ℕ) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => if r ≤ i.val+j.val+1 then 1 else 0

 theorem det_antiTriangle_succ (r : ℕ) :
    (antiTriangle (R:=R) (r+1)).det=(-1 : R)^r*(antiTriangle (R:=R) r).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last r)]
  · have hm : (antiTriangle (R:=R) (r+1)).submatrix Fin.succ (Fin.last r).succAbove=
        antiTriangle (R:=R) r := by
      ext i j
      simp only [antiTriangle, Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last,
        Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> first | rfl | omega
    rw [hm]
    simp [antiTriangle]
  · intro j _ hj
    have hlt : j.val<r := by
      have hj' : j.val≠r := by intro h; apply hj; exact Fin.ext h
      omega
    simp [antiTriangle, show ¬r≤j.val by omega]
  · simp

 theorem det_antiTriangle_even_odd (k : ℕ) :
    (antiTriangle (R:=R) (2*k)).det=(-1 : R)^k ∧
    (antiTriangle (R:=R) (2*k+1)).det=(-1 : R)^k := by
  induction k with
  | zero => simp [antiTriangle, Matrix.det_unique]
  | succ k ih =>
    have he : (antiTriangle (R:=R) (2*(k+1))).det=(-1 : R)^(k+1) := by
      rw [show 2*(k+1)=(2*k+1)+1 by omega, det_antiTriangle_succ, ih.2]
      simp [pow_add, pow_mul]
    refine ⟨he, ?_⟩
    rw [det_antiTriangle_succ, he]
    simp [pow_mul]

 theorem det_antiTriangle (r : ℕ) :
    (antiTriangle (R:=R) r).det=(-1 : R)^(r/2) := by
  have h := det_antiTriangle_even_odd (R:=R) (r/2)
  have he : r=2*(r/2) ∨ r=2*(r/2)+1 := by omega
  rcases he with he | he
  · exact (congrArg (fun n => (antiTriangle (R:=R) n).det) he).trans h.1
  · exact (congrArg (fun n => (antiTriangle (R:=R) n).det) he).trans h.2

 theorem det_antiTriangle_sq (r : ℕ) :
    ((antiTriangle (R:=R) r).det)^2=1 := by
  rw [det_antiTriangle, ← pow_mul, Nat.mul_comm, pow_mul]
  simp

end HankelAutomaticity
