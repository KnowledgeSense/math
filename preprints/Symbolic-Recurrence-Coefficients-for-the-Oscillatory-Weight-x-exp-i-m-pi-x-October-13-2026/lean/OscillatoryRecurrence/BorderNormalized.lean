import OscillatoryRecurrence.BorderFirstCoefficient
import OscillatoryRecurrence.FactorialOddCorrection

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

def endpointBlockJet (a b c : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℚ[X] :=
  Matrix.of fun i j => match i,j with
  | Sum.inl i,Sum.inl j => indexedEndpointEntry i.val j.val c 0 0
  | Sum.inl i,Sum.inr j => indexedEndpointEntry i.val j.val c 0 1
  | Sum.inr i,Sum.inl j => indexedEndpointEntry i.val j.val c 1 0
  | Sum.inr i,Sum.inr j => indexedEndpointEntry i.val j.val c 1 1

def endpointNewColumn (a b c r f : ℕ) : (Fin a ⊕ Fin b) → ℚ[X]
  | Sum.inl i => indexedEndpointEntry i.val r c 0 f
  | Sum.inr i => indexedEndpointEntry i.val r c 1 f

theorem endpointBlockJet_zero (a b c : ℕ) :
    (endpointBlockJet a b c).map (fun p => p.coeff 0)=
      Matrix.fromBlocks ((2:ℚ) • factorialMatrix a) 0 0 ((2:ℚ) • factorialMatrix b) := by
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [endpointBlockJet,indexedEndpointEntry_coeff_zero,factorialMatrix,one_add_one_eq_two]

theorem det_block_update_inl {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α α ℚ) (B : Matrix β β ℚ)
    (j : α) (v : α ⊕ β → ℚ) :
    ((Matrix.fromBlocks A 0 0 B).updateCol (Sum.inl j) v).det=
      (A.updateCol j (fun i => v (Sum.inl i))).det*B.det := by
  let D : Matrix β α ℚ := Matrix.of fun i k => if k=j then v (Sum.inr i) else 0
  have h : (Matrix.fromBlocks A 0 0 B).updateCol (Sum.inl j) v=
      Matrix.fromBlocks (A.updateCol j (fun i => v (Sum.inl i))) 0 D B := by
    apply Matrix.ext
    intro i k
    rcases i with i|i <;> rcases k with k|k <;>
      simp [Matrix.updateCol_apply,D]
  rw [h,Matrix.det_fromBlocks_zero₁₂]

theorem factorial_update_det (n : ℕ) (v : Fin (n+1) → ℚ) :
    ((factorialMatrix (n+1)).updateCol (Fin.last n) v).det=
      (factorialMatrix (n+1)).det*factorialLastFunctional n v := by
  have h := congrFun ((factorialMatrix (n+1)).det_smul_inv_mulVec_eq_cramer v
    (factorialMatrix_unit (n+1))) (Fin.last n)
  exact h.symm

def oddElimination (n : ℕ) : Fin (n+2) ⊕ Fin (n+1) → ℚ
  | Sum.inl _ => 0
  | Sum.inr j => factorialProjection (n+1) j

theorem oddElimination_constant (n : ℕ) :
    (fun i => (endpointNewColumn (n+2) (n+1) (n+1) (n+1) 1 i).coeff 0)=
      ((endpointBlockJet (n+2) (n+1) (n+1)).map (fun p => p.coeff 0))*ᵥoddElimination n := by
  rw [endpointBlockJet_zero]
  funext i
  rcases i with i|i
  · simp [endpointNewColumn,indexedEndpointEntry_coeff_zero,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,oddElimination]
  · have h := congrFun (factorialProjection_system (n+1)) i
    have hh := congrArg (fun q : ℚ => 2*q) h
    simpa [endpointNewColumn,indexedEndpointEntry_coeff_zero,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,oddElimination,factorialMatrix,mul_sum,mul_assoc,one_add_one_eq_two] using hh.symm

theorem residual_sum_split {ι : Type*} [Fintype ι] (A : ℚ) (c b v : ι → ℚ) :
    (∑ j, -2*(A+b j)*v j*c j)=
      -2*A*(∑ j,c j*v j)-2*(∑ j,c j*b j*v j) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem oddElimination_linear_inl (n : ℕ) (i : Fin (n+2)) :
    ((fun r => (endpointNewColumn (n+2) (n+1) (n+1) (n+1) 1 r).coeff 1)-
      ((endpointBlockJet (n+2) (n+1) (n+1)).map (fun p => p.coeff 1))*ᵥoddElimination n)
        (Sum.inl i)= -2*oddBorderCorrection n i.val := by
  let A : ℚ := ((n+1+i.val)%2:ℕ)+1+(i.val:ℚ)/2
  let B : ℚ := 1+(n+1:ℚ)/2
  let b : Fin (n+1) → ℚ := fun j => ((n+1+j.val+1)%2:ℕ)+(j.val:ℚ)/2
  have hv : (endpointNewColumn (n+2) (n+1) (n+1) (n+1) 1 (Sum.inl i)).coeff 1=
      -2*(A+B)*((i.val+n+2).factorial:ℚ) := by
    rw [endpointNewColumn,indexedEndpointEntry_coeff_one]
    have hp : (n+1+(n+1)+1)%2=1 := by omega
    rw [hp]
    dsimp [A,B]
    norm_num only [Nat.add_zero,Nat.zero_add,pow_one,sub_neg_eq_add,one_add_one_eq_two]
    push_cast
    rw [show i.val+(n+1)+1=i.val+n+2 by omega]
    ring
  have hm (j : Fin (n+1)) :
      ((endpointBlockJet (n+2) (n+1) (n+1) (Sum.inl i) (Sum.inr j)).coeff 1)=
        -2*(A+b j)*((i.val+j.val+1).factorial:ℚ) := by
    change (indexedEndpointEntry i.val j.val (n+1) 0 1).coeff 1=_
    rw [indexedEndpointEntry_coeff_one]
    dsimp [A,b]
    norm_num only [Nat.add_zero,Nat.zero_add,pow_one,sub_neg_eq_add,one_add_one_eq_two]
    push_cast
    ring
  simp only [Pi.sub_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    oddElimination,Matrix.map_apply,mul_zero,sum_const_zero,zero_add,hv,hm]
  rw [residual_sum_split]
  have hd := factorialProjection_shifted_defect n i.val
  change ((i.val+n+2).factorial:ℚ)-∑j : Fin (n+1),
    factorialProjection (n+1) j*((i.val+j.val+1).factorial:ℚ)=factorialShiftDefect n i.val at hd
  rw [oddBorderCorrection,← hd]
  change -2*(A+B)*((i.val+n+2).factorial:ℚ)-
    (-2*A*(∑j : Fin (n+1),factorialProjection (n+1) j*((i.val+j.val+1).factorial:ℚ))-
      2*(∑j : Fin (n+1),factorialProjection (n+1) j*b j*((i.val+j.val+1).factorial:ℚ)))=
    -2*(A*(((i.val+n+2).factorial:ℚ)-∑j : Fin (n+1),factorialProjection (n+1) j*((i.val+j.val+1).factorial:ℚ))+
      B*((i.val+n+2).factorial:ℚ)-∑j : Fin (n+1),factorialProjection (n+1) j*b j*((i.val+j.val+1).factorial:ℚ))
  ring

def oddNormalizedBorder (n : ℕ) : ℚ[X] :=
  ((endpointBlockJet (n+2) (n+1) (n+1)).updateCol (Sum.inl (Fin.last (n+1)))
    (endpointNewColumn (n+2) (n+1) (n+1) (n+1) 1)).det

theorem oddNormalizedBorder_coefficients (n : ℕ) :
    (oddNormalizedBorder n).coeff 0=0 ∧
    (oddNormalizedBorder n).coeff 1=
      -(3*(n+1:ℚ)^2+5*(n+1)+2)*
        ((endpointBlockJet (n+2) (n+1) (n+1)).map (fun p => p.coeff 0)).det := by
  have h := border_first_coefficients (endpointBlockJet (n+2) (n+1) (n+1))
    (Sum.inl (Fin.last (n+1))) (endpointNewColumn (n+2) (n+1) (n+1) (n+1) 1)
    (oddElimination n) rfl (oddElimination_constant n)
  refine ⟨h.1, ?_⟩
  unfold oddNormalizedBorder
  rw [h.2,endpointBlockJet_zero,det_block_update_inl]
  have hv : (fun i : Fin (n+2) =>
      ((fun r => (endpointNewColumn (n+2) (n+1) (n+1) (n+1) 1 r).coeff 1)-
      ((endpointBlockJet (n+2) (n+1) (n+1)).map (fun p => p.coeff 1))*ᵥoddElimination n)
        (Sum.inl i))=fun i => -2*oddBorderCorrection n i.val := by
    funext i
    exact oddElimination_linear_inl n i
  rw [hv]
  have he : ((2:ℚ) • factorialMatrix (n+2)).updateCol (Fin.last (n+1))
      (fun i => -2*oddBorderCorrection n i.val)=
      (2:ℚ) • ((factorialMatrix (n+2)).updateCol (Fin.last (n+1))
        (fun i => -oddBorderCorrection n i.val)) := by
    apply Matrix.ext
    intro i j
    by_cases hj : j=Fin.last (n+1) <;> simp [hj]
  rw [he,Matrix.det_smul,factorial_update_det]
  have hn : factorialLastFunctional (n+1) (fun i => -oddBorderCorrection n i.val)=
      -(3*(n+1:ℚ)^2+5*(n+1)+2) := by
    have hh := factorialLastFunctional_smul (n+1) (-1) (fun i => oddBorderCorrection n i.val)
    rw [oddBorderCorrection_functional] at hh
    have hneg : (-1:ℚ) • (fun i : Fin (n+2) => oddBorderCorrection n i.val)=
        (fun i => -oddBorderCorrection n i.val) := by funext i; simp
    rw [hneg] at hh
    simpa only [neg_one_mul] using hh
  rw [hn,Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_smul,Fintype.card_fin]
  ring

end OscillatoryRecurrence
