import OscillatoryRecurrence.BorderOdd

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

def borderLeadingFactor (n : ℕ) : ℚ :=
  if n%2=0 then 2*((n/2:ℕ):ℚ)^2
  else 3*((n/2:ℕ):ℚ)^2+5*((n/2:ℕ):ℚ)+2

@[simp] theorem borderLeadingFactor_even (k : ℕ) :
    borderLeadingFactor (2*k)=2*(k:ℚ)^2 := by simp [borderLeadingFactor]

@[simp] theorem borderLeadingFactor_odd (k : ℕ) :
    borderLeadingFactor (2*k+1)=3*(k:ℚ)^2+5*k+2 := by
  simp [borderLeadingFactor,Nat.add_div]

theorem borderLeadingFactor_pos (n : ℕ) (hn : 0<n) : 0<borderLeadingFactor n := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · rw [borderLeadingFactor_even]
    have hk : 0<k := by omega
    positivity
  · rw [borderLeadingFactor_odd]
    positivity

def borderEndpointOrder (n : ℕ) : ℕ :=
  (∑ i : Fin n,i.val/2)+(∑ j : Fin n,borderColumn n j/2)+n

theorem borderColumn_half_sum (n : ℕ) :
    (∑ j : Fin (n+1),borderColumn (n+1) j/2)=
      (∑ j : Fin n,j.val/2)+(n+1)/2 := by
  rw [Fin.sum_univ_castSucc]
  have hl : borderColumn (n+1) (Fin.last n)=n+1 := by simp [borderColumn]
  rw [hl]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [borderColumn,Fin.val_castSucc,ite_eq_right (by have := j.isLt; omega : j.val+1≠n+1)]

theorem borderEndpointOrder_succ (n : ℕ) :
    borderEndpointOrder (n+1)+n/2=endpointOrder (n+1)+(n+1)/2 := by
  unfold borderEndpointOrder endpointOrder
  rw [borderColumn_half_sum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  omega

theorem borderEndpointOrder_even (k : ℕ) :
    borderEndpointOrder (2*(k+1))=endpointOrder (2*(k+1))+1 := by
  have h := borderEndpointOrder_succ (2*k+1)
  rw [show 2*k+1+1=2*(k+1) by omega] at h
  omega

theorem borderEndpointOrder_odd (k : ℕ) :
    borderEndpointOrder (2*k+1)=endpointOrder (2*k+1) := by
  have h := borderEndpointOrder_succ (2*k)
  omega

theorem endpointBorder_factor (n : ℕ) (hn : 0<n) :
    endpointBorder n=X^(borderEndpointOrder n)*
      (Matrix.of (fun i j : Fin n => endpointEntry i.val (borderColumn n j))).det := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  exact endpointBorder_basis_factor k

theorem raw_border_odd_coefficients (k : ℕ) :
    ((Matrix.of (fun i j : Fin (2*k+1) => endpointEntry i.val (borderColumn (2*k+1) j))).det).coeff 0=0 ∧
    ((Matrix.of (fun i j : Fin (2*k+1) => endpointEntry i.val (borderColumn (2*k+1) j))).det).coeff 1=
      -(3*(k:ℚ)^2+5*k+2)*(endpointConstantMatrix (2*k+1)).det := by
  cases k with
  | zero =>
    norm_num only [Nat.mul_zero,Nat.zero_add,Nat.cast_zero]
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply,borderColumn,Fin.val_zero,Nat.zero_add,ite_true]
    change (endpointEntry 0 1).coeff 0=0 ∧
      (endpointEntry 0 1).coeff 1= -2*(endpointConstantMatrix 1).det
    constructor
    · rw [coeff_zero_eq_eval_zero,endpointEntry_eval_zero]
      norm_num
    · rw [endpointEntry_coeff_one]
      have h : (endpointConstantMatrix 1).det=2 := by
        rw [endpointConstantMatrix,Matrix.det_fin_one]
        change (endpointEntry 0 0).eval 0=2
        rw [endpointEntry_eval_zero]
        norm_num
      rw [h]
      norm_num
  | succ k =>
    simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using odd_border_coefficients k

theorem endpointBorder_order_coeff (n : ℕ) (hn : 0<n) :
    (endpointBorder n).coeff (endpointOrder n+1)=
      -borderLeadingFactor n*(endpointConstantMatrix n).det := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    simp only [Nat.succ_eq_add_one] at hn ⊢
    rw [endpointBorder_factor _ hn,borderEndpointOrder_even]
    have h := coeff_X_pow_mul
      ((Matrix.of (fun i j : Fin (2*(k+1)) => endpointEntry i.val (borderColumn (2*(k+1)) j))).det)
      (endpointOrder (2*(k+1))+1) 0
    simp only [zero_add] at h
    rw [h,coeff_zero_eq_eval_zero]
    have he := (Polynomial.evalRingHom (0:ℚ)).map_det
      (Matrix.of (fun i j : Fin (2*(k+1)) => endpointEntry i.val (borderColumn (2*(k+1)) j)))
    change (eval 0 ((Matrix.of (fun i j : Fin (2*(k+1)) =>
      endpointEntry i.val (borderColumn (2*(k+1)) j))).det))=
      (endpointBorderConstantMatrix (2*(k+1))).det at he
    rw [he,endpointBorderConstantMatrix_even_det,borderLeadingFactor_even]
    push_cast
    ring
  · rw [endpointBorder_factor _ hn,borderEndpointOrder_odd,
      show endpointOrder (2*k+1)+1=1+endpointOrder (2*k+1) by omega,coeff_X_pow_mul]
    rw [(raw_border_odd_coefficients k).2,borderLeadingFactor_odd]

theorem endpointBorder_below_order (n j : ℕ) (hn : 0<n) (hj : j<endpointOrder n+1) :
    (endpointBorder n).coeff j=0 := by
  obtain ⟨k,rfl|rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
    simp only [Nat.succ_eq_add_one] at hn hj ⊢
    rw [endpointBorder_factor _ hn,borderEndpointOrder_even,coeff_X_pow_mul',
      ite_eq_right (by omega)]
  · rw [endpointBorder_factor _ hn,borderEndpointOrder_odd]
    by_cases hh : j<endpointOrder (2*k+1)
    · rw [coeff_X_pow_mul',ite_eq_right (by omega)]
    · have he : j=endpointOrder (2*k+1) := by omega
      rw [he]
      have h := coeff_X_pow_mul
        ((Matrix.of (fun i j : Fin (2*k+1) => endpointEntry i.val (borderColumn (2*k+1) j))).det)
        (endpointOrder (2*k+1)) 0
      simp only [zero_add] at h
      rw [h,(raw_border_odd_coefficients k).1]

theorem endpointBorder_reflect_degree (n : ℕ) (hn : 0<n) :
    ((endpointBorder n).reflect (n^2+1)).natDegree=2*hankelDegree n := by
  have ho := endpointOrder_degree n
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_reflect]
    by_cases hjn : j≤n^2+1
    · rw [revAt_le hjn]
      exact endpointBorder_below_order n _ hn (by omega)
    · rw [revAt_eq_self_of_lt (by omega)]
      exact coeff_eq_zero_of_natDegree_lt ((endpointBorder_degree n).trans_lt (by omega))
  · rw [coeff_reflect,revAt_le (by omega : 2*hankelDegree n≤n^2+1),
      show n^2+1-2*hankelDegree n=endpointOrder n+1 by omega,endpointBorder_order_coeff n hn]
    exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt (borderLeadingFactor_pos n hn)))
      (ne_of_gt (endpointConstantMatrix_det_pos n))

theorem polynomialBorder_natDegree (n : ℕ) (hn : 0<n) :
    (polynomialBorder n).natDegree=hankelDegree n := by
  have h := endpointBorder_reflect_degree n hn
  rw [endpointBorder_reflect,natDegree_neg,natDegree_comp,natDegree_neg,natDegree_X_pow] at h
  omega

theorem polynomialBorder_leadingCoeff (n : ℕ) (hn : 0<n) :
    (polynomialBorder n).leadingCoeff=borderLeadingFactor n*(polynomialHankel n).leadingCoeff := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (2*hankelDegree n)) (endpointBorder_reflect n)
  have ho := endpointOrder_degree n
  rw [coeff_reflect,revAt_le (by omega : 2*hankelDegree n≤n^2+1),
    show n^2+1-2*hankelDegree n=endpointOrder n+1 by omega,endpointBorder_order_coeff n hn] at h
  have hnq : (-(X:ℚ[X])^2).natDegree=2 := by simp
  have hc := coeff_comp_degree_mul_degree (p := polynomialBorder n) (q := -(X:ℚ[X])^2)
    (by rw [hnq]; norm_num)
  rw [polynomialBorder_natDegree n hn,hnq,Nat.mul_comm] at hc
  have hl : (-(X:ℚ[X])^2).leadingCoeff=(-1:ℚ) := by simp
  rw [coeff_neg,hc,hl] at h
  rw [polynomialHankel_leadingCoeff]
  have hs : ((-1:ℚ)^hankelDegree n)^2=1 := by
    rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]
    norm_num
  linear_combination (-1:ℚ)^hankelDegree n*h-(polynomialBorder n).leadingCoeff*hs

end OscillatoryRecurrence
