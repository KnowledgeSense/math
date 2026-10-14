import HankelAutomaticity.BlockElimination

noncomputable section
namespace HankelAutomaticity
open Matrix

 def tailIndex (a : ℕ) {b : ℕ} (i : Fin b) : Fin (a+b+1) := ⟨a+1+i.val, by omega⟩

 def tailShear (a b : ℕ) : Matrix (Fin (a+b+1) ⊕ Unit) (Fin b) ℚ :=
  Matrix.of fun i j => match i with
    | Sum.inl i => if i.val=a+1+j.val then 1/2 else 0
    | Sum.inr _ => 0

 theorem tailShear_mul_high {a b : ℕ} {c : Type*} (P : Matrix (Fin b) c ℚ)
    (i : Fin b) (j : c) :
    (tailShear a b*P) (Sum.inl (tailIndex a i)) j=(1/2)*P i j := by
  simp only [Matrix.mul_apply, tailShear, Matrix.of_apply, tailIndex,
    Nat.add_left_cancel_iff]
  have he (k : Fin b) : i.val=k.val ↔ k=i := by constructor <;> intro h; exact Fin.ext h.symm; simp [h]
  simp [he]

 theorem tailShear_mul_low {a b : ℕ} {c : Type*} (P : Matrix (Fin b) c ℚ)
    (i : Fin (a+b+1)) (hi : i.val<a+1) (j : c) :
    (tailShear a b*P) (Sum.inl i) j=0 := by
  simp only [Matrix.mul_apply, tailShear, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [ite_eq_right (by omega), zero_mul]

 theorem tailShear_mul_unit {a b : ℕ} {c : Type*} (P : Matrix (Fin b) c ℚ) (i : Unit) (j : c) :
    (tailShear a b*P) (Sum.inr i) j=0 := by
  simp [Matrix.mul_apply, tailShear]

 theorem mul_tailShear_transpose_high {a b : ℕ} {c : Type*} (P : Matrix c (Fin b) ℚ)
    (i : c) (j : Fin b) :
    (P*(tailShear a b).transpose) i (Sum.inl (tailIndex a j))=(1/2)*P i j := by
  have h := tailShear_mul_high P.transpose j i (a:=a)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using h

 theorem mul_tailShear_transpose_low {a b : ℕ} {c : Type*} (P : Matrix c (Fin b) ℚ)
    (i : c) (j : Fin (a+b+1)) (hj : j.val<a+1) :
    (P*(tailShear a b).transpose) i (Sum.inl j)=0 := by
  have h := tailShear_mul_low P.transpose j hj i
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using h

 theorem mul_tailShear_transpose_unit {a b : ℕ} {c : Type*} (P : Matrix c (Fin b) ℚ) (i : c) (j : Unit) :
    (P*(tailShear a b).transpose) i (Sum.inr j)=0 := by
  have h := tailShear_mul_unit P.transpose j i (a:=a)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using h

 theorem index_low_or_tail {a b : ℕ} (i : Fin (a+b+1)) :
    i.val<a+1 ∨ ∃ j : Fin b, i=tailIndex a j := by
  by_cases hi : i.val<a+1
  · exact Or.inl hi
  · refine Or.inr ⟨⟨i.val-(a+1), by omega⟩, ?_⟩
    apply Fin.ext
    simp [tailIndex]
    omega

end HankelAutomaticity
