import OscillatoryRecurrence.FactorialBorder

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

def factorialMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => ((i.val+j.val).factorial:ℚ))

theorem factorialMatrix_det (n : ℕ) : (factorialMatrix n).det=laguerreConstant n :=
  factorialMoment_det n

theorem factorialMatrix_unit (n : ℕ) : IsUnit (factorialMatrix n).det := by
  rw [factorialMatrix_det]
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (laguerreConstant_pos n))

def factorialProjection (n : ℕ) : Fin n → ℚ :=
  (factorialMatrix n)⁻¹ *ᵥ (fun i => ((i.val+n).factorial:ℚ))

theorem factorialProjection_system (n : ℕ) :
    factorialMatrix n *ᵥ factorialProjection n = fun i => ((i.val+n).factorial:ℚ) := by
  rw [factorialProjection,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (factorialMatrix_unit n),Matrix.one_mulVec]

theorem factorialProjection_top (n : ℕ) :
    factorialProjection (n+1) (Fin.last n)=(n+1:ℚ)^2 := by
  have h := congrFun ((factorialMatrix (n+1)).det_smul_inv_mulVec_eq_cramer
    (fun i => ((i.val+(n+1)).factorial:ℚ)) (factorialMatrix_unit (n+1))) (Fin.last n)
  have he : (factorialMatrix (n+1)).updateCol (Fin.last n)
      (fun i => ((i.val+(n+1)).factorial:ℚ)) =
      Matrix.of (fun i j => ((i.val+borderColumn (n+1) j).factorial:ℚ)) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.updateCol_apply,factorialMatrix,Matrix.of_apply,borderColumn]
    by_cases hj : j=Fin.last n
    · subst j; simp
    · have hv : j.val≠n := by intro hh; apply hj; apply Fin.ext; simp; omega
      simp [hj,hv]
  change (factorialMatrix (n+1)).det*factorialProjection (n+1) (Fin.last n)=
    ((factorialMatrix (n+1)).updateCol (Fin.last n) _).det at h
  rw [he] at h
  erw [factorial_zero_border_ratio] at h
  apply mul_left_cancel₀ (factorialMatrix_unit (n+1)).ne_zero
  change (factorialMatrix (n+1)).det*factorialProjection (n+1) (Fin.last n)=
    (n+1:ℚ)^2*(factorialMatrix (n+1)).det at h
  simpa only [mul_comm] using h

def factorialProjectionPolynomial (n : ℕ) : ℚ[X] :=
  ∑ j : Fin n, C (factorialProjection n j)*ascPochhammer ℚ j.val

theorem factorialProjectionPolynomial_degree (n : ℕ) :
    (factorialProjectionPolynomial (n+1)).natDegree≤n := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans (by rw [ascPochhammer_natDegree]; have := j.isLt; omega)

theorem factorialProjectionPolynomial_eval (n : ℕ) (i : Fin n) :
    (factorialProjectionPolynomial n).eval ((i.val+1:ℕ):ℚ)=
      (ascPochhammer ℚ n).eval ((i.val+1:ℕ):ℚ) := by
  have h := congrFun (factorialProjection_system n) i
  apply mul_left_cancel₀ (by positivity : (i.val.factorial:ℚ)≠0)
  simp only [factorialProjectionPolynomial,eval_finsetSum,eval_mul,eval_C,mul_sum]
  rw [← factorial_zero_entry]
  change (∑ j : Fin n, (i.val.factorial:ℚ)*(factorialProjection n j*
    (ascPochhammer ℚ j.val).eval ((i.val+1:ℕ):ℚ)))=_
  simpa only [Matrix.mulVec,dotProduct,factorialMatrix,Matrix.of_apply,
    factorial_zero_entry,mul_left_comm,mul_comm,mul_assoc] using h

theorem factorialProjectionPolynomial_eq (n : ℕ) :
    factorialProjectionPolynomial (n+1)=factorialRemainder n := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f := fun i : Fin (n+1) => ((i.val+1:ℕ):ℚ))
  · intro i j h
    apply Fin.ext
    dsimp only at h
    have hh : i.val+1=j.val+1 := by exact_mod_cast h
    omega
  · intro i
    rw [factorialProjectionPolynomial_eval,factorialRemainder_eval]
  · simp only [Fintype.card_fin]
    exact max_lt (Nat.lt_succ_of_le (factorialProjectionPolynomial_degree n))
      (Nat.lt_succ_of_le (factorialRemainder_degree_le n))

theorem factorialProjection_defect (n r : ℕ) :
    ((r+n+1).factorial:ℚ)-∑j : Fin (n+1), factorialProjection (n+1) j*((r+j.val).factorial:ℚ)=
      (r.factorial:ℚ)*(factorialRoots (n+1)).eval ((r+1:ℕ):ℚ) := by
  have h := congrArg (fun p : ℚ[X] => p.eval ((r+1:ℕ):ℚ)) (factorialProjectionPolynomial_eq n)
  simp only [factorialProjectionPolynomial,eval_finsetSum,eval_mul,eval_C,
    factorialRemainder,eval_sub] at h
  have he := congrArg (fun q : ℚ => (r.factorial:ℚ)*q) h
  rw [mul_sub] at he
  simp only [mul_sum] at he
  have hh (j : Fin (n+1)) : (r.factorial:ℚ)*(factorialProjection (n+1) j*
      (ascPochhammer ℚ j.val).eval ((r+1:ℕ):ℚ))=
      factorialProjection (n+1) j*((r+j.val).factorial:ℚ) := by
    rw [factorial_zero_entry]
    ring
  simp only [hh,← factorial_zero_entry] at he
  rw [show r+n+1=r+(n+1) by omega]
  linarith

theorem factorialRoots_eval_desc (n r : ℕ) :
    (factorialRoots n).eval ((r+1:ℕ):ℚ)=(r.descFactorial n:ℚ) := by
  rw [← descPochhammer_eval_eq_descFactorial ℚ r n,descPochhammer_eval_eq_prod_range]
  simp only [factorialRoots,eval_prod,eval_sub,eval_X,eval_C,Nat.cast_add,Nat.cast_one]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (r:ℚ)+1-((i:ℚ)+1)) n]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem factorialProjection_shifted_defect (n r : ℕ) :
    ((r+n+2).factorial:ℚ)-∑j : Fin (n+1), factorialProjection (n+1) j*((r+j.val+1).factorial:ℚ)=
      ((r+1).factorial:ℚ)*((r+1).descFactorial (n+1):ℚ) := by
  have h := factorialProjection_defect n (r+1)
  rw [factorialRoots_eval_desc] at h
  simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm 1] using h

theorem factorialMatrix_inverse_last (n : ℕ) :
    (factorialMatrix (n+1))⁻¹ (Fin.last n) (Fin.last n)=1/(n.factorial:ℚ)^2 := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv]
  change (factorialMatrix (n+1)).det⁻¹*(factorialMatrix (n+1)).adjugate (Fin.last n) (Fin.last n)=_
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_last,Fin.succAbove_last]
  have hs : (-1:ℚ)^(n+n)=1 := (show Even (n+n) from ⟨n, by omega⟩).neg_one_pow
  rw [hs,one_mul]
  have hm : (factorialMatrix (n+1)).submatrix Fin.castSucc Fin.castSucc=factorialMatrix n := rfl
  rw [hm,factorialMatrix_det,factorialMatrix_det,laguerreConstant_succ]
  field_simp [ne_of_gt (laguerreConstant_pos n)]

theorem factorialMatrix_inverse_penultimate (n : ℕ) :
    (factorialMatrix (n+2))⁻¹ (Fin.last (n+1)) (Fin.last n).castSucc=
      -(n+1:ℚ)^2/((n+1).factorial:ℚ)^2 := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv]
  change (factorialMatrix (n+2)).det⁻¹*
    (factorialMatrix (n+2)).adjugate (Fin.last (n+1)) (Fin.last n).castSucc=_
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_last,Fin.val_castSucc,Fin.succAbove_last]
  have hs : (-1:ℚ)^(n+(n+1)) = -1 := by
    exact (show Odd (n+(n+1)) from ⟨n, by omega⟩).neg_one_pow
  rw [hs]
  have hm : (factorialMatrix (n+2)).submatrix (Fin.last n).castSucc.succAbove Fin.castSucc=
      (Matrix.of (fun i j : Fin (n+1) => ((i.val+borderColumn (n+1) j).factorial:ℚ)))ᵀ := by
    apply Matrix.ext
    intro i j
    change ((((Fin.last n).castSucc.succAbove i).val+j.val).factorial:ℚ)=((j.val+borderColumn (n+1) i).factorial:ℚ)
    congr 1
    congr 1
    by_cases hi : i.val<n
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hi)]
      simp only [Fin.val_castSucc,borderColumn,ite_eq_right (by omega : i.val+1≠n+1)]
      omega
    · rw [Fin.succAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt hi)]
      have hie : i.val=n := by have := i.isLt; omega
      simp [Fin.val_succ,borderColumn,hie]
      omega
  rw [hm,Matrix.det_transpose]
  erw [factorial_zero_border_ratio]
  change (factorialMatrix (n+2)).det⁻¹*(-1*((n+1:ℚ)^2*(factorialMatrix (n+1)).det))=_
  rw [factorialMatrix_det,factorialMatrix_det,laguerreConstant_succ (n+1)]
  field_simp [ne_of_gt (laguerreConstant_pos (n+1))]

end OscillatoryRecurrence
