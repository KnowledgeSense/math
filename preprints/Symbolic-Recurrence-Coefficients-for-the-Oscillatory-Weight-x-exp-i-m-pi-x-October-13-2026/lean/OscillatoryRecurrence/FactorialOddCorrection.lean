import OscillatoryRecurrence.FactorialOrthogonality

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

def factorialLastFunctional (n : ℕ) (v : Fin (n+1) → ℚ) : ℚ :=
  ((factorialMatrix (n+1))⁻¹ *ᵥ v) (Fin.last n)

theorem factorialLastFunctional_add (n : ℕ) (v w : Fin (n+1) → ℚ) :
    factorialLastFunctional n (v+w)=factorialLastFunctional n v+factorialLastFunctional n w := by
  simp [factorialLastFunctional,Matrix.mulVec_add]

theorem factorialLastFunctional_sub (n : ℕ) (v w : Fin (n+1) → ℚ) :
    factorialLastFunctional n (v-w)=factorialLastFunctional n v-factorialLastFunctional n w := by
  simp [factorialLastFunctional,Matrix.mulVec_sub]

theorem factorialLastFunctional_smul (n : ℕ) (a : ℚ) (v : Fin (n+1) → ℚ) :
    factorialLastFunctional n (a • v)=a*factorialLastFunctional n v := by
  rw [factorialLastFunctional,Matrix.mulVec_smul]
  rfl

theorem factorialLastFunctional_column (n : ℕ) (j : Fin (n+1)) :
    factorialLastFunctional n (fun i => ((i.val+j.val).factorial:ℚ))=
      if j=Fin.last n then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (factorialMatrix (n+1))
    (factorialMatrix_unit (n+1))) (Fin.last n)) j
  simpa [factorialLastFunctional,Matrix.mulVec,dotProduct,Matrix.mul_apply,
    factorialMatrix,Matrix.one_apply,eq_comm] using h

theorem factorialLastFunctional_next (n : ℕ) :
    factorialLastFunctional n (fun i => ((i.val+(n+1)).factorial:ℚ))=(n+1:ℚ)^2 :=
  factorialProjection_top n

def factorialShiftDefect (n : ℕ) (r : ℕ) : ℚ :=
  ((r+1).factorial:ℚ)*((r+1).descFactorial (n+1):ℚ)

theorem factorialShiftDefect_low (n r : ℕ) (hr : r<n) : factorialShiftDefect n r=0 := by
  unfold factorialShiftDefect
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : r+1<n+1)]
  simp

theorem factorialShiftDefect_penultimate (n : ℕ) :
    factorialShiftDefect n n=((n+1).factorial:ℚ)^2 := by
  rw [factorialShiftDefect,Nat.descFactorial_self,pow_two]

theorem factorialShiftDefect_last (n : ℕ) :
    factorialShiftDefect n (n+1)=((n+2).factorial:ℚ)^2 := by
  have h := Nat.factorial_mul_descFactorial (by omega : n+1≤n+2)
  have he : (n+2).descFactorial (n+1)=(n+2).factorial := by
    simpa using h
  rw [factorialShiftDefect,show n+1+1=n+2 by omega,he,pow_two]

theorem factorialLastFunctional_weighted_defect (n : ℕ) :
    factorialLastFunctional (n+1) (fun i =>
      (((n+1+i.val)%2:ℕ)+1+(i.val:ℚ)/2)*factorialShiftDefect n i.val)=
      -(n+1:ℚ)^2*(2+(n:ℚ)/2)+(n+2:ℚ)^2*(1+(n+1:ℚ)/2) := by
  unfold factorialLastFunctional
  simp only [Matrix.mulVec,dotProduct]
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have hzn := Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin n))) (fun i _ =>
    show (factorialMatrix (n+1+1))⁻¹ (Fin.last (n+1)) i.castSucc.castSucc *
      ((((n+1+i.val)%2:ℕ)+1+(i.val:ℚ)/2)*factorialShiftDefect n i.val)=0 by
      rw [factorialShiftDefect_low n i.val i.isLt,mul_zero,mul_zero])
  rw [hzn,factorialShiftDefect_penultimate,factorialShiftDefect_last,
    factorialMatrix_inverse_last,factorialMatrix_inverse_penultimate]
  have hp : (n+1+n)%2=1 := by omega
  have hp' : (n+1+(n+1))%2=0 := by omega
  rw [hp,hp']
  simp only [Nat.cast_one,Nat.cast_zero,zero_add]
  rw [Nat.factorial_succ (n+1)]
  push_cast
  field_simp
  ring

theorem factorialLastFunctional_sum (n : ℕ) {ι : Type*} [Fintype ι]
    (a : ι → ℚ) (v : ι → Fin (n+1) → ℚ) :
    factorialLastFunctional n (fun r => ∑ j, a j*v j r)=
      ∑ j, a j*factorialLastFunctional n (v j) := by
  simp only [factorialLastFunctional,Matrix.mulVec,dotProduct,mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem factorialLastFunctional_shifted_column (n : ℕ) (j : Fin (n+1)) :
    factorialLastFunctional (n+1) (fun i => ((i.val+j.val+1).factorial:ℚ))=
      if j=Fin.last n then 1 else 0 := by
  have h := factorialLastFunctional_column (n+1) j.succ
  rw [← Fin.succ_last] at h
  simpa only [Fin.val_succ,Nat.add_assoc,Fin.succ_inj] using h

def oddBorderCorrection (n r : ℕ) : ℚ :=
  (((n+1+r)%2:ℕ)+1+(r:ℚ)/2)*factorialShiftDefect n r+
    (1+(n+1:ℚ)/2)*((r+n+2).factorial:ℚ)-
      ∑ j : Fin (n+1), factorialProjection (n+1) j*
        (((n+1+j.val+1)%2:ℕ)+(j.val:ℚ)/2)*((r+j.val+1).factorial:ℚ)

theorem oddBorderCorrection_functional (n : ℕ) :
    factorialLastFunctional (n+1) (fun r => oddBorderCorrection n r.val)=
      3*(n+1:ℚ)^2+5*(n+1)+2 := by
  have he : (fun r : Fin (n+2) => oddBorderCorrection n r.val)=
      ((fun r => (((n+1+r.val)%2:ℕ)+1+(r.val:ℚ)/2)*factorialShiftDefect n r.val)+
      (1+(n+1:ℚ)/2) • (fun r => ((r.val+(n+2)).factorial:ℚ)))-
      (fun r => ∑ j : Fin (n+1),
        (factorialProjection (n+1) j*(((n+1+j.val+1)%2:ℕ)+(j.val:ℚ)/2))*
          ((r.val+j.val+1).factorial:ℚ)) := by
    funext r
    simp only [oddBorderCorrection,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    congr 2
  rw [he,factorialLastFunctional_sub,factorialLastFunctional_add,
    factorialLastFunctional_smul,factorialLastFunctional_next,
    factorialLastFunctional_weighted_defect,factorialLastFunctional_sum]
  simp only [factorialLastFunctional_shifted_column,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',mem_univ,ite_true,Fin.val_last,factorialProjection_top]
  rw [show (n+1+n+1)%2=0 by omega]
  simp only [Nat.cast_zero,zero_add]
  push_cast
  ring

end OscillatoryRecurrence
