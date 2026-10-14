import OscillatoryRecurrence.EndpointBlocks
import OscillatoryRecurrence.NumeratorPolynomials

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

 def factorialEndpointBlock (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => (-2)^i.val*(-2)^j.val*2*((i.val+j.val).factorial:ℚ))

 def endpointConstantMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => (endpointEntry i.val j.val).eval 0)

 theorem endpointConstantMatrix_even (k : ℕ) :
    (endpointConstantMatrix (2*k)).submatrix (evenEndpointEquiv k 0) (evenEndpointEquiv k 0)=
      Matrix.fromBlocks (factorialEndpointBlock k) 0 0 (factorialEndpointBlock k) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · simpa [endpointConstantMatrix,evenEndpointEquiv,evenEndpointIndex,factorialEndpointBlock,one_add_one_eq_two]
      using endpointEntry_index_eval_zero i.val j.val 0 0 0
  · simpa [endpointConstantMatrix,evenEndpointEquiv,evenEndpointIndex]
      using endpointEntry_index_eval_zero i.val j.val 0 0 1
  · simpa [endpointConstantMatrix,evenEndpointEquiv,evenEndpointIndex]
      using endpointEntry_index_eval_zero i.val j.val 0 1 0
  · simpa [endpointConstantMatrix,evenEndpointEquiv,evenEndpointIndex,factorialEndpointBlock,one_add_one_eq_two]
      using endpointEntry_index_eval_zero i.val j.val 0 1 1

 theorem endpointConstantMatrix_odd (k : ℕ) :
    (endpointConstantMatrix (2*k+1)).submatrix (oddEndpointEquiv k) (oddEndpointEquiv k)=
      Matrix.fromBlocks (factorialEndpointBlock (k+1)) 0 0 (factorialEndpointBlock k) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · simpa [endpointConstantMatrix,oddEndpointEquiv,oddEndpointIndex,factorialEndpointBlock,one_add_one_eq_two]
      using endpointEntry_index_eval_zero i.val j.val k 0 0
  · simpa [endpointConstantMatrix,oddEndpointEquiv,oddEndpointIndex]
      using endpointEntry_index_eval_zero i.val j.val k 0 1
  · simpa [endpointConstantMatrix,oddEndpointEquiv,oddEndpointIndex]
      using endpointEntry_index_eval_zero i.val j.val k 1 0
  · simpa [endpointConstantMatrix,oddEndpointEquiv,oddEndpointIndex,factorialEndpointBlock,one_add_one_eq_two]
      using endpointEntry_index_eval_zero i.val j.val k 1 1

 theorem factorialEndpointBlock_det (n : ℕ) :
    (factorialEndpointBlock n).det=(2:ℚ)^(n^2)*laguerreConstant n := by
  let A : Matrix (Fin n) (Fin n) ℚ := Matrix.of (fun i j => ((i.val+j.val).factorial:ℚ))
  let B : Matrix (Fin n) (Fin n) ℚ := Matrix.of (fun i j => (-2)^j.val*A i j)
  have he : factorialEndpointBlock n=Matrix.of (fun i j => ((-2)^i.val*2)*B i j) := by
    apply Matrix.ext
    intro i j
    dsimp [factorialEndpointBlock,B,A]
    ring
  rw [he,Matrix.det_mul_column]
  have hb : B.det=(∏j : Fin n,(-2:ℚ)^j.val)*A.det := Matrix.det_mul_row _ A
  rw [hb,factorialMoment_det]
  simp only [prod_mul_distrib,prod_pow_eq_pow_sum,prod_const,card_univ,Fintype.card_fin]
  have hn := double_index_sum n
  have hs : (-2:ℚ)^(∑i : Fin n,i.val)*(-2)^(∑i : Fin n,i.val)=
      (2:ℚ)^((∑i : Fin n,i.val)*2) := by
    rw [← pow_two,← pow_mul,Nat.mul_comm _ 2,pow_mul]
    norm_num
    rw [show (4:ℚ)=2^2 by norm_num,← pow_mul]
  calc
    _ = ((-2:ℚ)^(∑i : Fin n,i.val)*(-2)^(∑i : Fin n,i.val)) *
        2^n*laguerreConstant n := by ring
    _ = _ := by rw [hs,← pow_add,hn]

 theorem endpointConstantMatrix_even_det (k : ℕ) :
    (endpointConstantMatrix (2*k)).det=(4:ℚ)^(k^2)*(laguerreConstant k)^2 := by
  rw [← Matrix.det_submatrix_equiv_self (evenEndpointEquiv k 0),endpointConstantMatrix_even,
    Matrix.det_fromBlocks_zero₂₁,factorialEndpointBlock_det]
  rw [show (4:ℚ)=2^2 by norm_num,← pow_mul,Nat.mul_comm 2 (k^2),pow_mul]
  ring

 theorem endpointConstantMatrix_odd_det (k : ℕ) :
    (endpointConstantMatrix (2*k+1)).det=
      2*(4:ℚ)^(k*(k+1))*laguerreConstant k*laguerreConstant (k+1) := by
  rw [← Matrix.det_submatrix_equiv_self (oddEndpointEquiv k),endpointConstantMatrix_odd,
    Matrix.det_fromBlocks_zero₂₁,factorialEndpointBlock_det,factorialEndpointBlock_det]
  have he : (k+1)^2+k^2=2*(k*(k+1))+1 := by ring
  calc
    _ = (2:ℚ)^((k+1)^2+k^2)*laguerreConstant k*laguerreConstant (k+1) := by
      rw [pow_add]
      ring
    _ = _ := by
      rw [he,pow_add,pow_mul]
      norm_num only [pow_one,show (2:ℚ)^2=4 by norm_num]
      ring

 def endpointOrder (n : ℕ) : ℕ := (∑ i : Fin n,i.val/2)+(∑ i : Fin n,i.val/2)+n

 theorem endpointOrder_succ (n : ℕ) :
    endpointOrder (n+1)=endpointOrder n+2*(n/2)+1 := by
  simp only [endpointOrder,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]
  omega

 theorem endpointOrder_degree (n : ℕ) : endpointOrder n+2*hankelDegree n=n^2 := by
  induction n with
  | zero => simp [endpointOrder,hankelDegree]
  | succ n ih =>
    rw [endpointOrder_succ,hankelDegree_succ]
    have he : n/2+(n+1)/2=n := by omega
    nlinarith

 theorem endpointHankel_factor (n : ℕ) :
    endpointHankel n=X^(endpointOrder n)*
      Matrix.det (Matrix.of (fun i j : Fin n => endpointEntry i.val j.val)) :=
    endpointBasis_determinant n

 theorem endpointHankel_order_coeff (n : ℕ) :
    (endpointHankel n).coeff (endpointOrder n)=(endpointConstantMatrix n).det := by
  rw [endpointHankel_factor]
  have he := coeff_X_pow_mul (Matrix.det (Matrix.of (fun i j : Fin n => endpointEntry i.val j.val)))
    (endpointOrder n) 0
  simp only [zero_add] at he
  rw [he,coeff_zero_eq_eval_zero]
  exact (Polynomial.evalRingHom (0:ℚ)).map_det _

 theorem endpointHankel_below_order (n k : ℕ) (hk : k<endpointOrder n) :
    (endpointHankel n).coeff k=0 := by
  rw [endpointHankel_factor,coeff_X_pow_mul',ite_eq_right (by omega)]

 theorem endpointConstantMatrix_det_pos (n : ℕ) : 0<(endpointConstantMatrix n).det := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · rw [endpointConstantMatrix_even_det]
    exact mul_pos (by positivity) (sq_pos_of_pos (laguerreConstant_pos k))
  · rw [endpointConstantMatrix_odd_det]
    exact mul_pos (mul_pos (mul_pos (by norm_num) (by positivity)) (laguerreConstant_pos k))
      (laguerreConstant_pos (k+1))

 theorem endpointHankel_reflect_degree (n : ℕ) :
    ((endpointHankel n).reflect (n^2)).natDegree=2*hankelDegree n := by
  have ho := endpointOrder_degree n
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_reflect]
    by_cases hkn : k≤n^2
    · rw [revAt_le hkn]
      exact endpointHankel_below_order n _ (by omega)
    · rw [revAt_eq_self_of_lt (by omega)]
      exact coeff_eq_zero_of_natDegree_lt ((endpointHankel_degree n).trans_lt (by omega))
  · rw [coeff_reflect,revAt_le (by omega : 2*hankelDegree n≤n^2),
      show n^2-2*hankelDegree n=endpointOrder n by omega,endpointHankel_order_coeff]
    exact ne_of_gt (endpointConstantMatrix_det_pos n)

/-- Exact degree of every original moment determinant polynomial. -/
theorem polynomialHankel_natDegree (n : ℕ) :
    (polynomialHankel n).natDegree=hankelDegree n := by
  have h := endpointHankel_reflect_degree n
  rw [endpointHankel_reflect,natDegree_comp,natDegree_neg,natDegree_X_pow] at h
  omega

 theorem polynomialHankel_leadingCoeff (n : ℕ) :
    (polynomialHankel n).leadingCoeff=(-1:ℚ)^(hankelDegree n)*(endpointConstantMatrix n).det := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (2*hankelDegree n)) (endpointHankel_reflect n)
  have ho := endpointOrder_degree n
  rw [coeff_reflect,revAt_le (by omega : 2*hankelDegree n≤n^2),
    show n^2-2*hankelDegree n=endpointOrder n by omega,endpointHankel_order_coeff] at h
  have hn : (-(X:ℚ[X])^2).natDegree=2 := by simp
  have hc := coeff_comp_degree_mul_degree (p := polynomialHankel n) (q := -(X:ℚ[X])^2)
    (by rw [hn]; norm_num)
  rw [polynomialHankel_natDegree,hn,Nat.mul_comm] at hc
  have hl : (-(X:ℚ[X])^2).leadingCoeff=(-1:ℚ) := by simp
  rw [hc,hl] at h
  have hs : ((-1:ℚ)^hankelDegree n)^2=1 := by
    rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]
    norm_num
  linear_combination -(-1:ℚ)^hankelDegree n*h-(polynomialHankel n).leadingCoeff*hs

end OscillatoryRecurrence
