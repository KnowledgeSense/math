import OscillatoryRecurrence.BorderNormalized
import OscillatoryRecurrence.BorderEven

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

theorem endpointEntry_index_scaled (r s c e f : ℕ) :
    endpointEntry (2*r+(c+r+e)%2) (2*s+(c+s+f)%2)=
      C ((-2:ℚ)^r)*(C ((-2:ℚ)^s)*indexedEndpointEntry r s c e f) := by
  unfold indexedEndpointEntry
  rw [← mul_assoc,← mul_assoc,← map_mul,← map_mul,← pow_add,
    mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (-2:ℚ)≠0)),map_one,one_mul]

def endpointBlockScale (a b : ℕ) : Fin a ⊕ Fin b → ℚ
  | Sum.inl i => (-2)^i.val
  | Sum.inr i => (-2)^i.val

def oddJetScale (k : ℕ) : ℚ := (∏ i : Fin (k+1) ⊕ Fin k, endpointBlockScale (k+1) k i)^2

theorem det_scaled_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℚ) (M : Matrix ι ι ℚ[X]) :
    (Matrix.of (fun i j => C (w i)*(C (w j)*M i j))).det=
      C ((∏i,w i)^2)*M.det := by
  let B : Matrix ι ι ℚ[X] := Matrix.of fun i j => C (w j)*M i j
  have hb : B.det=(∏j,C (w j))*M.det := Matrix.det_mul_row _ M
  have he : Matrix.of (fun i j => C (w i)*(C (w j)*M i j))=
      Matrix.of (fun i j => C (w i)*B i j) := rfl
  rw [he,Matrix.det_mul_column,hb]
  rw [← map_prod,map_pow]
  ring

theorem odd_endpoint_matrix_scaled (k : ℕ) :
    (Matrix.of (fun i j : Fin (2*k+1) => endpointEntry i.val j.val)).submatrix
      (oddEndpointEquiv k) (oddEndpointEquiv k)=
      Matrix.of (fun i j => C (endpointBlockScale (k+1) k i)*
        (C (endpointBlockScale (k+1) k j)*endpointBlockJet (k+1) k k i j)) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · exact endpointEntry_index_scaled i.val j.val k 0 0
  · exact endpointEntry_index_scaled i.val j.val k 0 1
  · exact endpointEntry_index_scaled i.val j.val k 1 0
  · exact endpointEntry_index_scaled i.val j.val k 1 1

theorem coeff_zero_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ[X]) : M.det.coeff 0=(M.map (fun p => p.coeff 0)).det := by
  simp_rw [coeff_zero_eq_eval_zero]
  exact (Polynomial.evalRingHom (0:ℚ)).map_det M

theorem endpointConstantMatrix_odd_scaled (k : ℕ) :
    (endpointConstantMatrix (2*k+1)).det=oddJetScale k*
      ((endpointBlockJet (k+1) k k).map (fun p => p.coeff 0)).det := by
  have h := congrArg (fun p : ℚ[X] => p.coeff 0)
    (det_scaled_polynomial (endpointBlockScale (k+1) k) (endpointBlockJet (k+1) k k))
  rw [← odd_endpoint_matrix_scaled,Matrix.det_submatrix_equiv_self,coeff_C_mul] at h
  rw [coeff_zero_det,coeff_zero_det] at h
  have hm : (Matrix.of (fun i j : Fin (2*k+1) => endpointEntry i.val j.val)).map
      (fun p => p.coeff 0)=endpointConstantMatrix (2*k+1) := by
    apply Matrix.ext
    intro i j
    exact coeff_zero_eq_eval_zero (endpointEntry i.val j.val)
  rw [hm] at h
  exact h

theorem oddEndpointEquiv_last (k : ℕ) :
    oddEndpointEquiv k (Sum.inl (Fin.last k))=Fin.last (2*k) := by
  apply Fin.ext
  simp only [oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex,Fin.val_last]
  omega

theorem borderColumn_odd_index (k : ℕ) (j : Fin (k+1) ⊕ Fin k) :
    borderColumn (2*k+1) (oddEndpointEquiv k j)=
      if j=Sum.inl (Fin.last k) then 2*k+1 else (oddEndpointEquiv k j).val := by
  have he : (oddEndpointEquiv k j).val+1=2*k+1 ↔ j=Sum.inl (Fin.last k) := by
    constructor
    · intro h
      apply (oddEndpointEquiv k).injective
      rw [oddEndpointEquiv_last]
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · intro h
      rw [h,oddEndpointEquiv_last]
      rfl
  simp only [borderColumn,he]

theorem odd_border_matrix_scaled (k : ℕ) :
    (Matrix.of (fun i j : Fin (2*k+1) => endpointEntry i.val (borderColumn (2*k+1) j))).submatrix
      (oddEndpointEquiv k) (oddEndpointEquiv k)=
      Matrix.of (fun i j => C (endpointBlockScale (k+1) k i)*
        (C (endpointBlockScale (k+1) k j)*
          ((endpointBlockJet (k+1) k k).updateCol (Sum.inl (Fin.last k))
            (endpointNewColumn (k+1) k k k 1)) i j)) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply,Matrix.of_apply,borderColumn_odd_index,Matrix.updateCol_apply]
  have hp : (k+k+1)%2=1 := by omega
  rcases i with i|i <;> rcases j with j|j
  · by_cases hj : j=Fin.last k
    · subst j
      simp only [ite_true,endpointBlockScale,endpointNewColumn,Fin.val_last]
      simpa only [oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex,Nat.add_zero,hp]
        using endpointEntry_index_scaled i.val k k 0 1
    · simp only [Sum.inl.injEq,ite_eq_right hj,endpointBlockScale,endpointBlockJet,
        Matrix.of_apply,oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex]
      exact endpointEntry_index_scaled i.val j.val k 0 0
  · simp only [Sum.inr_ne_inl,ite_false,endpointBlockScale,endpointBlockJet,
      Matrix.of_apply,oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex]
    exact endpointEntry_index_scaled i.val j.val k 0 1
  · by_cases hj : j=Fin.last k
    · subst j
      simp only [ite_true,endpointBlockScale,endpointNewColumn,Fin.val_last]
      simpa only [oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex,hp]
        using endpointEntry_index_scaled i.val k k 1 1
    · simp only [Sum.inl.injEq,ite_eq_right hj,endpointBlockScale,endpointBlockJet,
        Matrix.of_apply,oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex]
      exact endpointEntry_index_scaled i.val j.val k 1 0
  · simp only [Sum.inr_ne_inl,ite_false,endpointBlockScale,endpointBlockJet,
      Matrix.of_apply,oddEndpointEquiv,Equiv.ofBijective_apply,oddEndpointIndex]
    exact endpointEntry_index_scaled i.val j.val k 1 1

theorem odd_border_determinant_scaled (n : ℕ) :
    (Matrix.of (fun i j : Fin (2*(n+1)+1) =>
      endpointEntry i.val (borderColumn (2*(n+1)+1) j))).det=
      C (oddJetScale (n+1))*oddNormalizedBorder n := by
  rw [← Matrix.det_submatrix_equiv_self (oddEndpointEquiv (n+1)),odd_border_matrix_scaled,
    det_scaled_polynomial]
  rfl

theorem odd_border_coefficients (n : ℕ) :
    ((Matrix.of (fun i j : Fin (2*(n+1)+1) =>
      endpointEntry i.val (borderColumn (2*(n+1)+1) j))).det).coeff 0=0 ∧
    ((Matrix.of (fun i j : Fin (2*(n+1)+1) =>
      endpointEntry i.val (borderColumn (2*(n+1)+1) j))).det).coeff 1=
      -(3*(n+1:ℚ)^2+5*(n+1)+2)*(endpointConstantMatrix (2*(n+1)+1)).det := by
  rw [odd_border_determinant_scaled]
  simp only [coeff_C_mul]
  rw [(oddNormalizedBorder_coefficients n).1,(oddNormalizedBorder_coefficients n).2,
    endpointConstantMatrix_odd_scaled]
  constructor
  · ring
  · ring

end OscillatoryRecurrence
