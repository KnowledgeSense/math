import OscillatoryRecurrence.ConstantBorder
import OscillatoryRecurrence.EndpointBlocks

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence
 def factorialRoots (n : ℕ) : ℚ[X] :=
  ∏ i : Fin n, (X-C ((i.val+1 : ℕ):ℚ))

 theorem factorialRoots_monic (n : ℕ) : (factorialRoots n).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

 theorem factorialRoots_natDegree (n : ℕ) : (factorialRoots n).natDegree = n := by
  unfold factorialRoots
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]

 theorem factorialRoots_eval (n : ℕ) (i : Fin n) :
    (factorialRoots n).eval ((i.val+1 : ℕ):ℚ) = 0 := by
  simp only [factorialRoots, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

 theorem factorialRoots_nextCoeff (n : ℕ) :
    (factorialRoots n).nextCoeff = -∑ i : Fin n, ((i.val+1 : ℕ):ℚ) := by
  unfold factorialRoots
  rw [Polynomial.Monic.nextCoeff_prod _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.nextCoeff_X_sub_C, Finset.sum_neg_distrib]

 def factorialRemainder (n : ℕ) : ℚ[X] :=
  ascPochhammer ℚ (n+1)-factorialRoots (n+1)

 theorem factorialRemainder_degree_le (n : ℕ) :
    (factorialRemainder n).natDegree ≤ n := by
  have hd : (ascPochhammer ℚ (n+1)).degree = (factorialRoots (n+1)).degree := by
    rw [Polynomial.degree_eq_natDegree (monic_ascPochhammer ℚ (n+1)).ne_zero,
      Polynomial.degree_eq_natDegree (factorialRoots_monic (n+1)).ne_zero,
      ascPochhammer_natDegree,factorialRoots_natDegree]
  have h := Polynomial.degree_sub_lt_left hd (monic_ascPochhammer ℚ (n+1)).ne_zero
    ((monic_ascPochhammer ℚ (n+1)).trans (factorialRoots_monic (n+1)).symm)
  rw [Polynomial.degree_eq_natDegree (monic_ascPochhammer ℚ (n+1)).ne_zero,
    ascPochhammer_natDegree] at h
  by_cases hz : factorialRemainder n = 0
  · simp [hz]
  · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr h)


 theorem factorialRemainder_eval (n : ℕ) (i : Fin (n+1)) :
    (factorialRemainder n).eval ((i.val+1:ℕ):ℚ) =
      (ascPochhammer ℚ (n+1)).eval ((i.val+1:ℕ):ℚ) := by
  rw [factorialRemainder,Polynomial.eval_sub,factorialRoots_eval,sub_zero]

theorem factorialRemainder_top_coeff (n : ℕ) :
    (factorialRemainder n).coeff n = (n+1:ℚ)^2 := by
  have ha := ascPochhammer_nextCoeff (n+1)
  have hr := factorialRoots_nextCoeff (n+1)
  have hca : (ascPochhammer ℚ (n+1)).nextCoeff = (ascPochhammer ℚ (n+1)).coeff n := by
    simp [Polynomial.nextCoeff,ascPochhammer_natDegree]
  have hcr : (factorialRoots (n+1)).nextCoeff = (factorialRoots (n+1)).coeff n := by
    simp [Polynomial.nextCoeff,factorialRoots_natDegree]
  rw [hca] at ha
  rw [hcr] at hr
  have hs : (∑ i : Fin (n+1), (i.val:ℚ))*2+(n+1:ℚ)=(n+1:ℚ)^2 := by
    exact_mod_cast double_index_sum (n+1)
  have hsum : (∑ i : Fin (n+1), ((i.val+1:ℕ):ℚ)) =
      (∑ i : Fin (n+1), (i.val:ℚ))+(n+1) := by
    simp only [Nat.cast_add,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    ring
  rw [hsum] at hr
  simp only [factorialRemainder,Polynomial.coeff_sub]
  push_cast at ha
  linarith

def factorialBorderBasis (n : ℕ) (j : Fin (n+1)) : ℚ[X] :=
  if j.val=n then factorialRemainder n else ascPochhammer ℚ j.val

 theorem factorialBorderBasis_degree (n : ℕ) (j : Fin (n+1)) :
    (factorialBorderBasis n j).natDegree ≤ j.val := by
  unfold factorialBorderBasis
  split_ifs with h
  · rw [h]; exact factorialRemainder_degree_le n
  · rw [ascPochhammer_natDegree]

 theorem factorialBorderBasis_eval (n : ℕ) (i j : Fin (n+1)) :
    (factorialBorderBasis n j).eval ((i.val+1:ℕ):ℚ) =
      (ascPochhammer ℚ (borderColumn (n+1) j)).eval ((i.val+1:ℕ):ℚ) := by
  have he : j.val+1=n+1 ↔ j.val=n := by omega
  simp only [factorialBorderBasis,borderColumn,he]
  split_ifs
  · exact factorialRemainder_eval n i
  · rfl

 theorem factorialBorderBasis_diag_prod (n : ℕ) :
    (∏ j : Fin (n+1), (factorialBorderBasis n j).coeff j.val) = (n+1:ℚ)^2 := by
  rw [Fin.prod_univ_castSucc]
  have hl : (factorialBorderBasis n (Fin.last n)).coeff (Fin.last n).val = (n+1:ℚ)^2 := by
    simp only [factorialBorderBasis,Fin.val_last]
    exact factorialRemainder_top_coeff n
  rw [hl]
  have hh : (∏ j : Fin n, (factorialBorderBasis n j.castSucc).coeff j.castSucc.val) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp only [factorialBorderBasis,Fin.val_castSucc,ite_eq_right (ne_of_lt j.is_lt)]
    have hc : (ascPochhammer ℚ j.val).coeff (ascPochhammer ℚ j.val).natDegree = 1 := by
      rw [Polynomial.coeff_natDegree]
      exact monic_ascPochhammer ℚ j.val
    simpa only [ascPochhammer_natDegree] using hc
  rw [hh,one_mul]

 theorem factorial_zero_entry (a b : ℕ) :
    ((a+b).factorial:ℚ) =
      (a.factorial:ℚ)*(ascPochhammer ℚ b).eval ((a+1:ℕ):ℚ) := by
  rw [ascPochhammer_nat_eq_natCast_ascFactorial]
  exact_mod_cast (Nat.factorial_mul_ascFactorial a b).symm

 theorem factorial_zero_border_ratio (n : ℕ) :
    Matrix.det (fun i j : Fin (n+1) =>
      ((i.val+borderColumn (n+1) j).factorial:ℚ)) =
    ((n+1:ℚ)^2)*Matrix.det (fun i j : Fin (n+1) =>
      ((i.val+j.val).factorial:ℚ)) := by
  let v : Fin (n+1) → ℚ := fun i => (i.val+1:ℕ)
  let E : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
    Matrix.of (fun i j => (ascPochhammer ℚ j.val).eval (v i))
  let F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
    Matrix.of (fun i j => (factorialBorderBasis n j).eval (v i))
  have he : E.det = (Matrix.vandermonde v).det :=
    (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => ascPochhammer ℚ j.val) (fun j => ascPochhammer_natDegree ℚ j.val)
      (fun j => monic_ascPochhammer ℚ j.val)).symm
  have hf : F.det = (Matrix.vandermonde v).det*((n+1:ℚ)^2) := by
    rw [show F = Matrix.of (fun i j => (factorialBorderBasis n j).eval (v i)) from rfl,
      det_eval_degree_bounded v (factorialBorderBasis n) (factorialBorderBasis_degree n),factorialBorderBasis_diag_prod]
  have ha : (fun i j : Fin (n+1) => ((i.val+j.val).factorial:ℚ)) =
      Matrix.of (fun i j => (i.val.factorial:ℚ)*E i j) := by
    ext i j; exact factorial_zero_entry i.val j.val
  have hb : (fun i j : Fin (n+1) => ((i.val+borderColumn (n+1) j).factorial:ℚ)) =
      Matrix.of (fun i j => (i.val.factorial:ℚ)*F i j) := by
    ext i j
    dsimp [F,v]
    rw [factorialBorderBasis_eval]
    exact factorial_zero_entry i.val (borderColumn (n+1) j)
  rw [ha,hb,Matrix.det_mul_column,Matrix.det_mul_column,he,hf]
  ring


end OscillatoryRecurrence
