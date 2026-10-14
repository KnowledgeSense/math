import OscillatoryRecurrence.BorderBasis
import OscillatoryRecurrence.FactorialOrthogonality
import OscillatoryRecurrence.EndpointHankelLeading

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

def endpointBorderConstantMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (endpointEntry i.val (borderColumn n j)).eval 0

def factorialEndpointBorderBlock (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j => (-2)^i.val*(-2)^(borderColumn (n+1) j)*2*
    ((i.val+borderColumn (n+1) j).factorial:ℚ)

theorem factorialEndpointBorderBlock_det (n : ℕ) :
    (factorialEndpointBorderBlock n).det=
      (-2*(n+1:ℚ)^2)*(factorialEndpointBlock (n+1)).det := by
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ := Matrix.of fun i j =>
    ((i.val+borderColumn (n+1) j).factorial:ℚ)
  let B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ := Matrix.of fun i j => (-2)^(borderColumn (n+1) j)*A i j
  have he : factorialEndpointBorderBlock n=Matrix.of (fun i j => ((-2)^i.val*2)*B i j) := by
    apply Matrix.ext
    intro i j
    dsimp [factorialEndpointBorderBlock,B,A]
    ring
  rw [he,Matrix.det_mul_column]
  have hb : B.det=(∏j : Fin (n+1),(-2:ℚ)^(borderColumn (n+1) j))*A.det := Matrix.det_mul_row _ A
  rw [hb]
  have hA : A.det=(n+1:ℚ)^2*(factorialMatrix (n+1)).det := by
    exact factorial_zero_border_ratio n
  rw [hA]
  have hp : (∏j : Fin (n+1),(-2:ℚ)^(borderColumn (n+1) j))=
      (-2)*(∏j : Fin (n+1),(-2:ℚ)^j.val) := by
    rw [prod_pow_eq_pow_sum,prod_pow_eq_pow_sum,borderColumn_sum _ (by omega),pow_succ]
    ring
  rw [hp]
  have hF : (factorialEndpointBlock (n+1)).det=
      (∏i : Fin (n+1),(-2:ℚ)^i.val*2)*
        (∏j : Fin (n+1),(-2:ℚ)^j.val)*(factorialMatrix (n+1)).det := by
    have he' : factorialEndpointBlock (n+1)=Matrix.of (fun i j =>
        ((-2)^i.val*2)*((-2)^j.val*factorialMatrix (n+1) i j)) := by
      apply Matrix.ext
      intro i j
      dsimp [factorialEndpointBlock,factorialMatrix]
      ring
    rw [he']
    erw [Matrix.det_mul_column,Matrix.det_mul_row]
    ring
  rw [hF]
  ring

theorem even_border_left_index (n : ℕ) (j : Fin (n+1)) :
    borderColumn (2*(n+1)) (evenEndpointEquiv (n+1) (n+1) (Sum.inl j))=
      2*borderColumn (n+1) j+((n+1)+borderColumn (n+1) j)%2 := by
  simp only [evenEndpointEquiv,Equiv.ofBijective_apply,evenEndpointIndex]
  unfold borderColumn
  dsimp only
  have hj := j.isLt
  split_ifs <;> omega

theorem even_border_right_index (n : ℕ) (j : Fin (n+1)) :
    borderColumn (2*(n+1)) (evenEndpointEquiv (n+1) (n+1) (Sum.inr j))=
      2*j.val+((n+1)+j.val+1)%2 := by
  simp only [evenEndpointEquiv,Equiv.ofBijective_apply,evenEndpointIndex]
  unfold borderColumn
  dsimp only
  have hj := j.isLt
  split_ifs <;> omega

theorem endpointBorderConstantMatrix_even (n : ℕ) :
    (endpointBorderConstantMatrix (2*(n+1))).submatrix
      (evenEndpointEquiv (n+1) (n+1)) (evenEndpointEquiv (n+1) (n+1))=
      Matrix.fromBlocks (factorialEndpointBorderBlock n) 0 0 (factorialEndpointBlock (n+1)) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · change (endpointEntry _ (borderColumn _ _)).eval 0=_
    rw [even_border_left_index]
    change (endpointEntry (2*i.val+((n+1)+i.val)%2)
      (2*borderColumn (n+1) j+((n+1)+borderColumn (n+1) j)%2)).eval 0=_
    simpa [factorialEndpointBorderBlock,one_add_one_eq_two] using
      endpointEntry_index_eval_zero i.val (borderColumn (n+1) j) (n+1) 0 0
  · change (endpointEntry _ (borderColumn _ _)).eval 0=_
    rw [even_border_right_index]
    simpa [evenEndpointEquiv,evenEndpointIndex] using
      endpointEntry_index_eval_zero i.val j.val (n+1) 0 1
  · change (endpointEntry _ (borderColumn _ _)).eval 0=_
    rw [even_border_left_index]
    simpa [evenEndpointEquiv,evenEndpointIndex] using
      endpointEntry_index_eval_zero i.val (borderColumn (n+1) j) (n+1) 1 0
  · change (endpointEntry _ (borderColumn _ _)).eval 0=_
    rw [even_border_right_index]
    simpa [evenEndpointEquiv,evenEndpointIndex,factorialEndpointBlock,one_add_one_eq_two] using
      endpointEntry_index_eval_zero i.val j.val (n+1) 1 1

theorem endpointBorderConstantMatrix_even_det (n : ℕ) :
    (endpointBorderConstantMatrix (2*(n+1))).det=
      (-2*(n+1:ℚ)^2)*(endpointConstantMatrix (2*(n+1))).det := by
  rw [← Matrix.det_submatrix_equiv_self (evenEndpointEquiv (n+1) (n+1)),
    endpointBorderConstantMatrix_even,Matrix.det_fromBlocks_zero₂₁,
    factorialEndpointBorderBlock_det]
  rw [← Matrix.det_submatrix_equiv_self (evenEndpointEquiv (n+1) 0)
    (endpointConstantMatrix (2*(n+1))),endpointConstantMatrix_even,
    Matrix.det_fromBlocks_zero₂₁]
  ring

end OscillatoryRecurrence
