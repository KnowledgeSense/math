import OscillatoryRecurrence.Nonvanishing

noncomputable section
open Polynomial Finset
open scoped BigOperators
namespace OscillatoryRecurrence

 def interpolationRoots (n : ℕ) : ℚ[X] :=
  ∏ i : Fin n, (X-C ((i.val+2 : ℕ):ℚ))

 theorem interpolationRoots_monic (n : ℕ) : (interpolationRoots n).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

 theorem interpolationRoots_natDegree (n : ℕ) : (interpolationRoots n).natDegree = n := by
  unfold interpolationRoots
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]

 theorem interpolationRoots_eval (n : ℕ) (i : Fin n) :
    (interpolationRoots n).eval ((i.val+2 : ℕ):ℚ) = 0 := by
  simp only [interpolationRoots, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

 theorem interpolationRoots_nextCoeff (n : ℕ) :
    (interpolationRoots n).nextCoeff = -∑ i : Fin n, ((i.val+2 : ℕ):ℚ) := by
  unfold interpolationRoots
  rw [Polynomial.Monic.nextCoeff_prod _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.nextCoeff_X_sub_C, Finset.sum_neg_distrib]

 theorem ascPochhammer_nextCoeff (n : ℕ) :
    2*(ascPochhammer ℚ n).nextCoeff = (n:ℚ)*((n:ℚ)-1) := by
  induction n with
  | zero => norm_num [ascPochhammer,Polynomial.nextCoeff]
  | succ n ih =>
    rw [ascPochhammer_succ_right,
      Polynomial.Monic.nextCoeff_mul (monic_ascPochhammer ℚ n)
        (by simpa only [← Polynomial.C_eq_natCast] using Polynomial.monic_X_add_C (n:ℚ))]
    have hn : (X+(n:ℚ[X])).nextCoeff=(n:ℚ) := by
      simpa only [Polynomial.C_eq_natCast] using Polynomial.nextCoeff_X_add_C (n:ℚ)
    rw [hn]
    push_cast
    linear_combination ih

 def interpolationRemainder (n : ℕ) : ℚ[X] :=
  ascPochhammer ℚ (n+1)-interpolationRoots (n+1)

 theorem interpolationRemainder_degree_le (n : ℕ) :
    (interpolationRemainder n).natDegree ≤ n := by
  have hd : (ascPochhammer ℚ (n+1)).degree = (interpolationRoots (n+1)).degree := by
    rw [Polynomial.degree_eq_natDegree (monic_ascPochhammer ℚ (n+1)).ne_zero,
      Polynomial.degree_eq_natDegree (interpolationRoots_monic (n+1)).ne_zero,
      ascPochhammer_natDegree,interpolationRoots_natDegree]
  have h := Polynomial.degree_sub_lt_left hd (monic_ascPochhammer ℚ (n+1)).ne_zero
    ((monic_ascPochhammer ℚ (n+1)).trans (interpolationRoots_monic (n+1)).symm)
  rw [Polynomial.degree_eq_natDegree (monic_ascPochhammer ℚ (n+1)).ne_zero,
    ascPochhammer_natDegree] at h
  by_cases hz : interpolationRemainder n = 0
  · simp [hz]
  · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr h)


 theorem interpolationRemainder_eval (n : ℕ) (i : Fin (n+1)) :
    (interpolationRemainder n).eval ((i.val+2:ℕ):ℚ) =
      (ascPochhammer ℚ (n+1)).eval ((i.val+2:ℕ):ℚ) := by
  rw [interpolationRemainder,Polynomial.eval_sub,interpolationRoots_eval,sub_zero]

theorem interpolationRemainder_top_coeff (n : ℕ) :
    (interpolationRemainder n).coeff n = (n+1:ℚ)*(n+2) := by
  have ha := ascPochhammer_nextCoeff (n+1)
  have hr := interpolationRoots_nextCoeff (n+1)
  have hca : (ascPochhammer ℚ (n+1)).nextCoeff = (ascPochhammer ℚ (n+1)).coeff n := by
    simp [Polynomial.nextCoeff,ascPochhammer_natDegree]
  have hcr : (interpolationRoots (n+1)).nextCoeff = (interpolationRoots (n+1)).coeff n := by
    simp [Polynomial.nextCoeff,interpolationRoots_natDegree]
  rw [hca] at ha
  rw [hcr] at hr
  have hs : (∑ i : Fin (n+1), (i.val:ℚ))*2+(n+1:ℚ)=(n+1:ℚ)^2 := by
    exact_mod_cast double_index_sum (n+1)
  have hsum : (∑ i : Fin (n+1), ((i.val+2:ℕ):ℚ)) =
      (∑ i : Fin (n+1), (i.val:ℚ))+2*(n+1) := by
    simp only [Nat.cast_add,Nat.cast_ofNat,Finset.sum_add_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    ring
  rw [hsum] at hr
  simp only [interpolationRemainder,Polynomial.coeff_sub]
  push_cast at ha
  linarith

 theorem det_eval_degree_bounded (v : Fin n → ℚ) (p : Fin n → ℚ[X])
    (hdeg : ∀ j, (p j).natDegree ≤ j.val) :
    (Matrix.of (fun i j => (p j).eval (v i))).det =
      (Matrix.vandermonde v).det * ∏ j : Fin n, (p j).coeff j.val := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p hdeg,
    Matrix.det_mul,Matrix.det_of_isUpperTriangular
      (Matrix.matrixOfPolynomials_isUpperTriangular p hdeg)]
  rfl

def borderBasis (n : ℕ) (j : Fin (n+1)) : ℚ[X] :=
  if j.val=n then interpolationRemainder n else ascPochhammer ℚ j.val

 theorem borderBasis_degree (n : ℕ) (j : Fin (n+1)) :
    (borderBasis n j).natDegree ≤ j.val := by
  unfold borderBasis
  split_ifs with h
  · rw [h]; exact interpolationRemainder_degree_le n
  · rw [ascPochhammer_natDegree]

 theorem borderBasis_eval (n : ℕ) (i j : Fin (n+1)) :
    (borderBasis n j).eval ((i.val+2:ℕ):ℚ) =
      (ascPochhammer ℚ (borderColumn (n+1) j)).eval ((i.val+2:ℕ):ℚ) := by
  have he : j.val+1=n+1 ↔ j.val=n := by omega
  simp only [borderBasis,borderColumn,he]
  split_ifs
  · exact interpolationRemainder_eval n i
  · rfl

 theorem borderBasis_diag_prod (n : ℕ) :
    (∏ j : Fin (n+1), (borderBasis n j).coeff j.val) = (n+1:ℚ)*(n+2) := by
  rw [Fin.prod_univ_castSucc]
  have hl : (borderBasis n (Fin.last n)).coeff (Fin.last n).val = (n+1:ℚ)*(n+2) := by
    simp only [borderBasis,Fin.val_last]
    exact interpolationRemainder_top_coeff n
  rw [hl]
  have hh : (∏ j : Fin n, (borderBasis n j.castSucc).coeff j.castSucc.val) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp only [borderBasis,Fin.val_castSucc,ite_eq_right (ne_of_lt j.is_lt)]
    have hc : (ascPochhammer ℚ j.val).coeff (ascPochhammer ℚ j.val).natDegree = 1 := by
      rw [Polynomial.coeff_natDegree]
      exact monic_ascPochhammer ℚ j.val
    simpa only [ascPochhammer_natDegree] using hc
  rw [hh,one_mul]

 theorem factorial_entry (a b : ℕ) :
    (2:ℚ)*(a+b+1).factorial =
      (2*((a+1).factorial:ℚ))*(ascPochhammer ℚ b).eval ((a+2:ℕ):ℚ) := by
  rw [ascPochhammer_nat_eq_natCast_ascFactorial]
  have h := Nat.factorial_mul_ascFactorial (a+1) b
  have hc : ((a+1).factorial:ℚ)*((a+2).ascFactorial b:ℚ)=((a+b+1).factorial:ℚ) := by
    exact_mod_cast h.trans (by congr 1; omega)
  linear_combination -2*hc

 theorem factorial_border_ratio (n : ℕ) :
    Matrix.det (fun i j : Fin (n+1) =>
      (2:ℚ)*(i.val+borderColumn (n+1) j+1).factorial) =
    ((n+1:ℚ)*(n+2))*Matrix.det (fun i j : Fin (n+1) =>
      (2:ℚ)*(i.val+j.val+1).factorial) := by
  let v : Fin (n+1) → ℚ := fun i => (i.val+2:ℕ)
  let E : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
    Matrix.of (fun i j => (ascPochhammer ℚ j.val).eval (v i))
  let F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
    Matrix.of (fun i j => (borderBasis n j).eval (v i))
  have he : E.det = (Matrix.vandermonde v).det :=
    (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j => ascPochhammer ℚ j.val) (fun j => ascPochhammer_natDegree ℚ j.val)
      (fun j => monic_ascPochhammer ℚ j.val)).symm
  have hf : F.det = (Matrix.vandermonde v).det*((n+1:ℚ)*(n+2)) := by
    rw [show F = Matrix.of (fun i j => (borderBasis n j).eval (v i)) from rfl,
      det_eval_degree_bounded v (borderBasis n) (borderBasis_degree n),borderBasis_diag_prod]
  have ha : (fun i j : Fin (n+1) => (2:ℚ)*(i.val+j.val+1).factorial) =
      Matrix.of (fun i j => (2*((i.val+1).factorial:ℚ))*E i j) := by
    ext i j; exact factorial_entry i.val j.val
  have hb : (fun i j : Fin (n+1) => (2:ℚ)*(i.val+borderColumn (n+1) j+1).factorial) =
      Matrix.of (fun i j => (2*((i.val+1).factorial:ℚ))*F i j) := by
    ext i j
    dsimp [F,v]
    rw [borderBasis_eval]
    exact factorial_entry i.val (borderColumn (n+1) j)
  rw [ha,hb,Matrix.det_mul_column,Matrix.det_mul_column,he,hf]
  ring

 theorem polynomialBorder_eval_zero (n : ℕ) :
    (polynomialBorder n).eval 0 = (n:ℚ)*(n+1)*(polynomialHankel n).eval 0 := by
  cases n with
  | zero => simp [polynomialBorder]
  | succ n =>
    have hJ := (Polynomial.evalRingHom (0:ℚ)).map_det
      (fun i j : Fin (n+1) => endpointMoment (i.val+borderColumn (n+1) j))
    have hH := (Polynomial.evalRingHom (0:ℚ)).map_det
      (fun i j : Fin (n+1) => endpointMoment (i.val+j.val))
    change (polynomialHankel (n+1)).eval 0 =
      Matrix.det (fun i j : Fin (n+1) => (endpointMoment (i.val+j.val)).eval 0) at hH
    change (polynomialBorder (n+1)).eval 0 =
      Matrix.det (fun i j : Fin (n+1) =>
        (endpointMoment (i.val+borderColumn (n+1) j)).eval 0) at hJ
    simp only [endpointMoment_eval_zero] at hJ hH
    rw [hJ,hH,factorial_border_ratio]
    push_cast
    ring

end OscillatoryRecurrence
